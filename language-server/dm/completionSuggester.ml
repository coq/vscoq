(**************************************************************************)
(*                                                                        *)
(*                                 VSCoq                                  *)
(*                                                                        *)
(*                   Copyright INRIA and contributors                     *)
(*       (see version control and README file for authors & dates)        *)
(*                                                                        *)
(**************************************************************************)
(*                                                                        *)
(*   This file is distributed under the terms of the MIT License.         *)
(*   See LICENSE file.                                                    *)
(*                                                                        *)
(**************************************************************************)
open Protocol

module CompactedDecl = Context.Compacted.Declaration
open Printer
open EConstr
open Names
open Types

let Log log = Log.mk_log "completionSuggester"

module TypeCompare = struct
  type t = types
  let compare = compare
end

let takeSkip n l = 
  let rec sub_list n accu l =
    match l with 
    | [] -> accu, [] 
    | hd :: tl ->
      if n = 0 then accu, tl
      else sub_list (n - 1) (hd :: accu) tl
  in
  let take, skip = sub_list n [] l in
  List.rev (take), skip


module Atomics = Set.Make(TypeCompare)

module HypothesisMap = Map.Make (struct type t = Id.t let compare = compare end)

let mk_hyp d (env,l) =
  let d' = CompactedDecl.to_named_context d in
  let env' = List.fold_right EConstr.push_named d' env in
  let ids, typ = match d with
  | CompactedDecl.LocalAssum (ids, typ) -> ids, typ
  | CompactedDecl.LocalDef (ids,_,typ) -> ids, typ
  in
  let ids' = List.map (fun id -> id.Context.binder_name) ids in
  let m = List.fold_right (fun id acc -> HypothesisMap.add id typ acc) ids' l in
  (env', m)

let get_hyps env sigma goal =
    let EvarInfo evi = Evd.find sigma goal in
    let env = Evd.evar_filtered_env env evi in
    let min_env = Environ.reset_context env in
    let (_env, hyps) =
      Context.Compacted.fold (mk_hyp)
        (Termops.compact_named_context sigma (EConstr.named_context env)) ~init:(min_env, HypothesisMap.empty) in
    hyps

let type_kind_opt sigma t = try Some (kind_of_type sigma t) with _ -> None 

let type_size sigma t : int = 
  let rec aux u = 
    match kind sigma u with
    | Sort _ -> 1
    | Cast (c,_,t) -> aux c + aux t
    | Prod (_,t,c) -> aux t + aux c
    | LetIn (_,b,t,c) -> aux b + aux t + aux c
    | App (c,l) -> Array.map aux l |> Array.fold_left (+) (aux c)
    | Rel _ -> 1
    | (Meta _ | Var _ | Evar _ | Const _
    | Proj _ | Case _ | Fix _ | CoFix _ | Ind _) -> 1
    | (Lambda _ | Construct _ | Array _ | Int _ | Float _) -> 1
  in
  aux t

module TypeIntersection = struct
  let atomic_types sigma t: Atomics.t = 
    let rec aux t : types list = 
      match (type_kind_opt sigma t) with
      | Some SortType _ -> [] (* Might be possible to get atomics from also *)
      | Some CastType (tt, t) -> aux tt @ aux t
      | Some ProdType (_, t1, t2) -> aux t1 @ aux t2
      | Some LetInType _ -> [] 
      | Some AtomicType (t, ta) ->
        t :: (Array.map aux ta |> Array.to_list |> List.flatten);
      | None -> [] (* Lol :) *)
      in
    aux t |>
    Atomics.of_list

  let compare_atomics (goal : Atomics.t) (a1, _ : Atomics.t * _) (a2, _ : Atomics.t * _) : int = 
    match (Atomics.inter a1 goal, Atomics.inter a2 goal) with
    | r1, r2 when Atomics.cardinal r1 = Atomics.cardinal r2 -> 
      (* If the size is equal, priotize the one with fewest types *)
      compare (Atomics.cardinal a1) (Atomics.cardinal a2)
    | r1, r2 -> 
      (* Return the set with largest overlap, so we sort in increasing order swap the arguments *)
      compare (Atomics.cardinal r2) (Atomics.cardinal r1)

  let split_types sigma c =
    let (list, other_c) = decompose_prod sigma c in 
    list 
    |> List.map snd
    |> List.cons other_c
    |> List.map (fun typ -> atomic_types sigma typ)
    |> List.fold_left (fun (acc, result) item -> (Atomics.union acc item, Atomics.union acc item :: result)) (Atomics.empty, [])
    |> snd

  let best_subtype sigma goal c = 
    c |> split_types sigma |> List.map (fun a -> (a, a)) |> List.stable_sort (compare_atomics goal) |> List.hd |> fst

  let rank (goal : Evd.econstr) sigma _ (lemmas : CompletionItems.completion_item list) : CompletionItems.completion_item list =
    (*Split type intersection: Split the lemmas by implications, compare the suffix to the goal, pick best match*)
    let goal = atomic_types sigma goal in
    let lemmaTypes = List.map (fun (l : CompletionItems.completion_item) -> 
      let best = best_subtype sigma goal (of_constr l.typ) in
      (best, l)
    ) lemmas in
    List.stable_sort (compare_atomics goal) lemmaTypes |> 
    List.map snd
end

type bruijn_level = int

module Structured = struct
  type unifier = 
    | SortUniType of ESorts.t * bruijn_level
    | AtomicUniType of types * unifier array

  let _print_unifier env sigma u =
    let po u = match kind sigma u with
    | Sort s -> Printf.eprintf "Sort: ";
      (match ESorts.kind sigma s with 
      | SProp -> Printf.eprintf "SProp\n";
      | Prop -> Printf.eprintf "Prop\n";
      | Set  -> Printf.eprintf "Set\n";
      | Type _ -> Printf.eprintf "Type\n";
      | QSort (_, _) -> Printf.eprintf "QSort\n";
      )
    | Cast (c,_,t) -> Printf.eprintf "cast: %s, %s\n" 
      (Pp.string_of_ppcmds (pr_econstr_env env sigma c))
      (Pp.string_of_ppcmds (pr_econstr_env env sigma t))
    | Prod (na,_,_) -> Printf.eprintf "Prod: %s\n"
      (Name.print na.binder_name |> Pp.string_of_ppcmds)
    | LetIn (_,b,t,c) -> 
      Printf.eprintf "LetIn: %s, %s, %s\n" 
        (Pp.string_of_ppcmds (pr_econstr_env env sigma b))
        (Pp.string_of_ppcmds (pr_econstr_env env sigma t))
        (Pp.string_of_ppcmds (pr_econstr_env env sigma c))
    | App (c,_) -> 
      Printf.eprintf "App: %s\n" 
        (Pp.string_of_ppcmds (pr_econstr_env env sigma c))
    | Rel i -> Printf.eprintf "Rel: %d\n" i
    | Meta _ -> Printf.eprintf "Meta: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    | Var _ -> Printf.eprintf "Var: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    | Evar _ -> Printf.eprintf "Evar: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    | Const _ -> Printf.eprintf "Const: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    | Proj _ -> Printf.eprintf "Proj: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    | Case _ -> Printf.eprintf "Case: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    | Fix _ -> Printf.eprintf "Fix: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    | CoFix _ -> Printf.eprintf "CoFix: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    | Ind _ -> Printf.eprintf "Ind: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    | Lambda _ -> Printf.eprintf "Lambda: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    | Construct _ -> Printf.eprintf "Construct: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    | Int _ -> Printf.eprintf "Int: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    | Float _ -> Printf.eprintf "Float: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    | Array _ -> Printf.eprintf "Array: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    in
    let rec aux i u = 
      Printf.eprintf "%s" (String.init i (fun _ -> ' '));
      match u with
      | SortUniType (s, i) -> Printf.eprintf "Sort %d: %s\n" i
        (match ESorts.kind sigma s with 
        | SProp -> "SProp"
        | Prop -> "Prop"
        | Set  -> "Set"
        | Type _ -> "Type"
        | QSort _ -> "QSort"
        )
      | AtomicUniType (t, ta) -> Printf.eprintf "Atomic: ";
        po t;
      Array.iter (aux (i+1)) ta
    in
    aux 0 u

  (* map from bruijn_level to unifier *)
  module UM = Map.Make(struct type t = bruijn_level let compare = compare end)

  (* This is extremely slow, we should not convert it to a list. *)
  let filter_options a = 
    a |> Array.to_list |> Option.List.flatten |> Array.of_list

  let _debug_print env sigma t : unit = 
    let rec aux i u = 
      Printf.eprintf "%s" (String.init i (fun _ -> ' '));
      match kind sigma u with
      | Sort s -> Printf.eprintf "Sort: ";
        (match ESorts.kind sigma s with 
        | SProp -> Printf.eprintf "SProp\n";
        | Prop -> Printf.eprintf "Prop\n";
        | Set  -> Printf.eprintf "Set\n";
        | Type _ -> Printf.eprintf "Type\n";
        | QSort (_, _) -> Printf.eprintf "QSort\n";
        )
      | Cast (c,_,t) -> Printf.eprintf "cast: %s, %s\n" 
        (Pp.string_of_ppcmds (pr_econstr_env env sigma c))
        (Pp.string_of_ppcmds (pr_econstr_env env sigma t))
      | Prod (na,t,c) -> Printf.eprintf "Prod: %s\n"
        (Name.print na.binder_name |> Pp.string_of_ppcmds);
        aux (i+1) t;
        aux (i+1) c
      | LetIn (_,b,t,c) -> 
        Printf.eprintf "LetIn: %s, %s, %s\n" 
          (Pp.string_of_ppcmds (pr_econstr_env env sigma b))
          (Pp.string_of_ppcmds (pr_econstr_env env sigma t))
          (Pp.string_of_ppcmds (pr_econstr_env env sigma c));
        aux (i+1) t;
        aux (i+1) c;
        aux (i+1) b
      | App (c,l) -> 
        Printf.eprintf "App: %s\n" 
          (Pp.string_of_ppcmds (pr_econstr_env env sigma c));
        Array.iter (aux (i+1)) l
      | Rel i -> Printf.eprintf "Rel: %d\n" i
      | Meta _ -> Printf.eprintf "Meta: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
      | Var _ -> Printf.eprintf "Var: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
      | Evar _ -> Printf.eprintf "Evar: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
      | Const _ -> Printf.eprintf "Const: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
      | Proj _ -> Printf.eprintf "Proj: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
      | Case _ -> Printf.eprintf "Case: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
      | Fix _ -> Printf.eprintf "Fix: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
      | CoFix _ -> Printf.eprintf "CoFix: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
      | Ind _ -> Printf.eprintf "Ind: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
      | Lambda _ -> Printf.eprintf "Lambda: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
      | Construct _ -> Printf.eprintf "Construct: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
      | Int _ -> Printf.eprintf "Int: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
      | Float _ -> Printf.eprintf "Float: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
      | Array _ -> Printf.eprintf "Array: %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma u))
    in
    aux 0 t

  let unifier_kind sigma (hyps : types HypothesisMap.t) (t : types) : unifier option =
    let rec aux bruijn t = match kind sigma t with
      | Sort s -> SortUniType (s, List.length bruijn) |> Option.make
      | Cast (c,_,_) -> aux bruijn c
      | Prod (_,t,c) -> aux (aux bruijn t :: bruijn) c (* Possibly the index should be assigned here instead and be a thing for both types. *)
      | LetIn (_,_,t,c) -> aux (aux bruijn t :: bruijn) c
      | App (c,l) -> 
        let l' = Array.map (aux bruijn) l in
        AtomicUniType (c, filter_options l') |> Option.make
      | Rel i -> List.nth bruijn (i-1)
      | Var v when HypothesisMap.mem v hyps -> aux bruijn (HypothesisMap.find v hyps)
      | (Meta _ | Var _ | Evar _ | Const _
      | Proj _ | Case _ | Fix _ | CoFix _ | Ind _)
        -> AtomicUniType (t,[||]) |> Option.make
      | (Lambda _ | Construct _ | Int _ | Float _ | Array _) -> None
    in
    aux [] t

  let rec matches evd (u1: unifier) (u2: unifier) =
    match (u1, u2) with
    | SortUniType (s1, _), SortUniType (s2, _) -> 
      ESorts.equal evd s1 s2
    | SortUniType _, _ -> false
    | _, SortUniType _ -> false (* TODO: Maybe add to UM? Maybe not? The UM is not the goal. *)
    | AtomicUniType (t1, ua1), AtomicUniType (t2, ua2) -> 
      let c = EConstr.compare_constr evd (EConstr.eq_constr evd) t1 t2 in
      if c then 
        let rec aux ua1 ua2 = 
          match (ua1, ua2) with
          | [], [] -> true
          | [], _ | _, [] -> false
          | u1 :: ua1, u2 :: ua2 -> 
            let c = matches evd u1 u2 in
            if c then aux ua1 ua2 else false
        in
        aux (Array.to_list ua1) (Array.to_list ua2)
      else false
  
  let score_unifier atomic_factor evd (goal : unifier) (u : unifier) : float =
    let rec aux (um : unifier UM.t) g u  : (float * unifier UM.t) = 
    match (g, u) with
      | SortUniType (s1, _), SortUniType (s2, _) -> if ESorts.equal evd s1 s2 then (1., um) else (0., um)
      (* We might want to check if the t in AtomicUniType actually belongs in the sort*)
      | SortUniType _, _ -> (0., um) (* If the goal has a sort then it has to match *)
      | AtomicUniType (_, _), SortUniType (s, i) ->
        if UM.mem i um then 
          let u = UM.find i um in
          matches evd u (SortUniType (s, i)) |> Bool.to_float |> fun x -> (x, um)
        else (1., UM.add i u um)
      | AtomicUniType (t1, ua1), AtomicUniType (t2, ua2) -> 
        let c = EConstr.compare_constr evd (EConstr.eq_constr evd) t1 t2 |> Bool.to_float |> (Float.mul atomic_factor) in
        let c = 
          if isVar evd t1 && isVar evd t2 then
            Float.mul c 2.0
          else c in
        if Array.length ua1 <> Array.length ua2 then (c, um)
        else 
          let (score, um) = Array.fold_left (fun (acc, um) (u1, u2) -> 
            let (s, um) = aux um u1 u2 in
            (Float.add acc s, um)
          ) (c, um) (Array.combine ua1 ua2) in
          (score, um)
    in
    aux UM.empty goal u |> fst

  let unpack_unifier u : unifier list = 
    let res = ref [] in
    let rec aux u = match u with
      | SortUniType (_, _) -> ();
      | AtomicUniType (_, ua) -> 
        res := u :: !res;
        Array.iter aux ua
    in
    aux u;
    !res

  let rec size_unifier u = match u with
    | SortUniType (_, _) -> 1l
    | AtomicUniType (_, ua) -> Array.fold_left (fun acc u -> Int32.add acc (size_unifier u)) 1l ua

  (* A Lower score is better as we are sorting in ascending order *)

  let rank (options: Settings.Completion.t) (goal, goal_evar) sigma env lemmas : CompletionItems.completion_item list =
    let size_impact = options.sizeFactor in
    let atomic_factor = options.atomicFactor in
    let finalScore score size = Float.sub size (Float.mul score size_impact) in
    let hyps = get_hyps env sigma goal_evar in
    match (unifier_kind sigma hyps goal, unifier_kind sigma HypothesisMap.empty goal) with
    | None, _ | _, None -> lemmas
    | Some goalUnf, Some goalUnfNoHypothesisSub -> 
      let lemmaUnfs = List.map (fun (l : CompletionItems.completion_item) -> 
        match (unifier_kind sigma HypothesisMap.empty (of_constr l.typ)) with
        | None -> ((Float.min_float), l)
        | Some unf -> 
          let scores = List.map (score_unifier atomic_factor sigma goalUnf) (unpack_unifier unf) in
          let scores = scores @ (List.map (score_unifier atomic_factor sigma goalUnfNoHypothesisSub) (unpack_unifier unf)) in
          let size = size_unifier unf |> Int32.to_float in
          let maxScore = List.fold_left Float.max 0. scores in
          let final = finalScore maxScore size in
          l.debug_info <- (Printf.sprintf "Score: %f, Size: %f, Final Score: %f" maxScore size final);
          (final, l)
      ) lemmas in
      let sorted = List.stable_sort (fun (x, _) (y, _) -> Float.compare x y) lemmaUnfs in
      List.map snd sorted
end
module SelectiveUnification = struct
  let rankByUnifiability (goal : Evd.econstr) sigma env (lemmas : CompletionItems.completion_item list) : CompletionItems.completion_item list =
    let goal_size = type_size sigma goal in
    let worst_value = 1000 in (* the worst value we expect to assign. This value is mostly arbitrary*)
    let make_sortable (lemma : CompletionItems.completion_item) =
      let flags = Evarconv.default_flags_of TransparentState.full in
      let rec aux (iterations: int) (typ : types) : (CompletionItems.completion_item * int)=
        if type_size sigma typ + goal_size > 500 then (lemma, worst_value) (*The number 500 is an arbitrary limit on how big lemmas we are willing to look at*)
        else
        let res = Evarconv.evar_conv_x flags env sigma Conversion.CONV goal typ in
        match res with
        | Success _ ->
          ({lemma with completes = if iterations = 0 then Some Fully else Some Partially}, iterations)
        | UnifFailure (_, _) ->
          match kind sigma typ with
          | Prod (_,_,c) -> aux (iterations + 1) c
          | Cast (c,_,_) -> aux iterations c
          | _            -> ({lemma with completes = Some No_completion}, worst_value)
        in
      try 
        aux 0 (of_constr lemma.typ)
      with e ->
        Printf.sprintf "Error in Split Unification: %s for %s\n%!" (Printexc.to_string e) (Pp.string_of_ppcmds (pr_global lemma.ref)) |> log;
        ({lemma with completes = Some No_completion}, worst_value)
     in
    lemmas
    |> List.map make_sortable
    |> List.stable_sort (fun a b -> compare (snd a) (snd b))
    |> List.map fst

  let selectiveRank (options: Settings.Completion.t) (goal : Evd.econstr) sigma env (lemmas : CompletionItems.completion_item list) : CompletionItems.completion_item list =
    try 
      let take, skip = takeSkip options.unificationLimit lemmas in
      List.append (rankByUnifiability goal sigma env take) skip
    with e ->
      log ("Error in Split Unification: %s" ^ (Printexc.to_string e));
      lemmas

  let rank = selectiveRank
end

let rank_choices (options: Settings.Completion.t) (goal, goal_evar) sigma env lemmas = 
  let open Settings.Completion.RankingAlgoritm in
  match options.algorithm with
  | SplitTypeIntersection -> TypeIntersection.rank goal sigma env lemmas
  | StructuredSplitUnification -> SelectiveUnification.rank options goal sigma env (Structured.rank options (goal, goal_evar) sigma env lemmas)

let get_goal_type_opt env Proof.{ goals; sigma; _ } =
  List.nth_opt goals 0
  |> Option.map (fun goal ->
    let evi = Evd.find_undefined sigma goal in
    let env = Evd.evar_filtered_env env evi in
    Evd.evar_concl evi, sigma, env, goal
    )

let get_completion_items env proof lemmas options =
  try 
    match get_goal_type_opt env proof with
    | None -> lemmas
    | Some (goal, sigma, env, goal_evar) ->
        rank_choices options (goal, goal_evar) sigma env lemmas
  with e -> 
    log ("Ranking of lemmas failed: " ^ (Printexc.to_string e));
    lemmas

let get_lemmas sigma env =
  let open CompletionItems in
  let results = ref [] in
  let display ref _kind env c =
    results := mk_completion_item sigma ref env c :: results.contents;
  in
  Search.generic_search env display;
  results.contents

let get_completions options st =
  Vernacstate.unfreeze_full_state st;
  match st.interp.lemmas with
  | None -> None
  | Some lemmas ->
    let proof = Proof.data (lemmas |> Vernacstate.LemmaStack.with_top ~f:Declare.Proof.get) in
    let env = Global.env () in
    let sigma = proof.sigma in
    let lemmas = get_lemmas sigma env in
    Some (get_completion_items env proof lemmas options)
