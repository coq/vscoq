module CompactedDecl = Context.Compacted.Declaration
open Printer
open EConstr
open Names
open Map

module TypeCompare = struct
  type t = types
  let compare = compare
end

module Atomics = Set.Make(TypeCompare)

let get_goal_type st loc =
  let goal, sigma = 
    match DocumentManager.get_proof st loc with
    | Some Proof.{ goals; sigma; _ } -> List.nth goals 0, sigma
    | None -> raise (Invalid_argument "goal") 
  in
  let evi = Evd.find_undefined sigma goal in
  let env = Evd.evar_filtered_env (Global.env ()) evi in
  (Evd.evar_concl evi, sigma, env)

let get_goal_type_option st loc =
  let proof = DocumentManager.get_proof st loc in
  Option.bind proof (fun Proof.{ goals; sigma; _ } -> 
    List.nth_opt goals 0 
    |> Option.map (fun goal ->
      let evi = Evd.find_undefined sigma goal in
      let env = Evd.evar_filtered_env (Global.env ()) evi in
      Evd.evar_concl evi, sigma, env
      )
    )

let type_kind_opt sigma t = try Some (kind_of_type sigma t) with exn -> None 

module SimpleAtomics = struct
  let atomic_types sigma t: Atomics.t = 
    let rec aux t : types list = 
      match (type_kind_opt sigma t) with
      | Some SortType t -> [] (* Might be possible to get atomics from also *)
      | Some CastType (tt, t) -> [] (* Dont know if we need this *)
      | Some ProdType (n, t1, t2) -> aux t1 @ aux t2
      | Some LetInType _ -> [] 
      | Some AtomicType (t, ta) ->
        t :: (Array.map aux ta |> Array.to_list |> List.flatten);
      | None -> [] (* Lol :) *)
      in
    aux t |>
    Atomics.of_list

  let debug_print_atomics env sigma atomics = 
    Atomics.fold (fun t l -> (Pp.string_of_ppcmds (pr_econstr_env env sigma t ) |> Printf.sprintf "%s") :: l) atomics [] |>
    String.concat "," |>
    Printf.eprintf "Atomics: [%s]\n"

  let compare_atomics (goal : Atomics.t) (a1, _ : Atomics.t * _) (a2, _ : Atomics.t * _) : int = 
    match (Atomics.inter a1 goal, Atomics.inter a2 goal) with
    | r1, r2 when Atomics.cardinal r1 = Atomics.cardinal r2 -> 
      (* If the size is equal, priotize the one with fewest types *)
      compare (Atomics.cardinal a1) (Atomics.cardinal a2)
    | r1, r2 -> 
      (* Return the set with largest overlap, so we sort in increasing order swap the arguments *)
      compare (Atomics.cardinal r2) (Atomics.cardinal r1)

  let rank (goal : Evd.econstr) sigma env lemmas : CompletionItems.completion_item list =
    let lemmaAtomics = List.map (fun (l : CompletionItems.completion_item) -> 
      (atomic_types sigma (of_constr l.typ), l)
    ) lemmas in
    let goalAtomics = atomic_types sigma goal in
    List.stable_sort (compare_atomics goalAtomics) lemmaAtomics |> 
    List.map snd 
end 

module Split = struct
  let split_types sigma c =
    let (list, other_c) = decompose_prod sigma c in 
    list 
    |> List.map snd
    |> List.cons other_c
    |> List.map (fun typ -> SimpleAtomics.atomic_types sigma typ)
    |> List.fold_left (fun (acc, result) item -> (Atomics.union acc item, Atomics.union acc item :: result)) (Atomics.empty, [])
    |> snd

  let best_subtype sigma goal c = 
    c |> split_types sigma |> List.map (fun a -> (a, a)) |> List.stable_sort (SimpleAtomics.compare_atomics goal) |> List.hd |> fst

  let rank (goal : Evd.econstr) sigma env lemmas : CompletionItems.completion_item list =
    (*Split type intersection: Split the lemmas by implications, compare the suffix to the goal, pick best match*)
    let goal = SimpleAtomics.atomic_types sigma goal in
    let lemmaTypes = List.map (fun (l : CompletionItems.completion_item) -> 
      let best = best_subtype sigma goal (of_constr l.typ) in
      (best, l)
    ) lemmas in
    List.stable_sort (SimpleAtomics.compare_atomics goal) lemmaTypes |> 
    List.map snd
end

type rev_bruijn_index = int



module Structured = struct
  type unifier = 
    | SortUniType of ESorts.t * rev_bruijn_index
    | AtomicUniType of types * unifier array

  (* map from rev_bruijn_index to unifier *)
  module UM = Map.Make(struct type t = rev_bruijn_index let compare = compare end)

  (* This is extremely slow, we should not convert it to a list. *)
  let filter_options a = 
    a |> Array.to_list |> Option.List.flatten |> Array.of_list

  let unifier_kind sigma (t : types) : unifier option = 
    let rec aux bruijn t = match kind sigma t with
      | Sort s -> SortUniType (s, List.length bruijn) |> Option.make
      | Cast (c,_,t) -> failwith "Not implemented"
      | Prod (na,t,c) -> aux (aux bruijn t :: bruijn) c (* Possibly the index should be assigned here instead and be a thing for both types. *)
      | LetIn (na,b,t,c) -> failwith "Not implemented"
      | App (c,l) -> 
        let l' = Array.map (aux bruijn) l in
        AtomicUniType (c, filter_options l') |> Option.make
      | Rel i -> List.nth bruijn (i-1)
      | (Meta _ | Var _ | Evar _ | Const _
      | Proj _ | Case _ | Fix _ | CoFix _ | Ind _)
        -> AtomicUniType (t,[||]) |> Option.make
      | (Lambda _ | Construct _ | Int _ | Float _ | Array _) -> None
    in
    aux [] t

  let debug_print_unifier env sigma t : unit = 
    let rec aux i u =
      Printf.eprintf "%s" (String.init i (fun _ -> ' '));
      match u with
      | SortUniType (s, i) -> Printf.eprintf "SortUniType (%d): " i;
        (match ESorts.kind sigma s with 
        | SProp -> Printf.eprintf "SProp\n";
        | Prop -> Printf.eprintf "Prop\n";
        | Set  -> Printf.eprintf "Set\n";
        | Type u -> Printf.eprintf "Type\n";
        | QSort (u, l) -> Printf.eprintf "QSort\n";
        )
      | AtomicUniType (t, ua) -> 
        Printf.eprintf "AtomicUniType %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma t));
        Array.iter (fun u -> aux (i + 1) u) ua
    in
    Option.iter (aux 0) (unifier_kind sigma t) 

  let debug_print_kind_of_type sigma env k: unit = 
    let rec aux i k = 
      Printf.eprintf "%s" (String.init i (fun _ -> ' '));
      match k with
      | Some SortType t -> 
        Printf.eprintf "SortType\n"; 
      | Some CastType (tt, t) ->
        Printf.eprintf "CastType\n"; 
      | Some ProdType (n, t1, t2) ->
        Printf.eprintf "ProdType %s\n" (Names.Name.print n.binder_name |> Pp.string_of_ppcmds); 
        aux (i+1) (type_kind_opt sigma t1);
        aux (i+1) (type_kind_opt sigma t2);
      | Some LetInType _ ->
        Printf.eprintf "LetInType\n"; 
      | Some AtomicType (t, ta) -> 
        Printf.eprintf "AtomicType %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma t)); 
        Array.iter (fun t -> type_kind_opt sigma t |> aux (i+1)) ta;
      | None -> () (* Lol :) *)
      in
    aux 0 k

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

  let atomicMatchFactor = 2.0
  
  let score_unifier use_um evd (goal : unifier) (u : unifier) : float =
    let rec aux (um : unifier UM.t) g u  : (float * unifier UM.t) = 
    match (g, u) with
      | SortUniType (s1, i1), SortUniType (s2, i2) -> if ESorts.equal evd s1 s2 then (1., um) else (0., um)
      (* We might want to check if the t in AtomicUniType actually belongs in the sort*)
      | SortUniType _, _ -> (0., um) (* If the goal has a sort then it has to match *)
      | AtomicUniType (t, ua), SortUniType (s, i) ->
        if UM.mem i um then 
          let u = UM.find i um in
          matches evd u (SortUniType (s, i)) |> Bool.to_float |> fun x -> (x, um)
        else (1., if use_um then UM.add i u um else um)
      | AtomicUniType (t1, ua1), AtomicUniType (t2, ua2) -> 
        let c = EConstr.compare_constr evd (EConstr.eq_constr evd) t1 t2 |> Bool.to_float |> (Float.mul atomicMatchFactor) in
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
      | SortUniType (s, i) -> ();
      | AtomicUniType (t, ua) -> 
        res := u :: !res;
        Array.iter aux ua
    in
    aux u;
    !res

  let size_unifier u = 
    let rec aux u = match u with
      | SortUniType (s, i) -> 1l
      | AtomicUniType (t, ua) -> Array.fold_left (fun acc u -> Int32.add acc (aux u)) 1l ua
    in
    aux u

  let finalScore score size = Float.sub size (Float.mul score 5.) 
  (* A Lower score is better as we are sorting in ascending order *)
  (* The 5 value is just a placeholder and has not been beenchmarked *)

  let rank use_um (goal : Evd.econstr) sigma env lemmas : CompletionItems.completion_item list =
    Printf.eprintf "Goal\n:";
    debug_print_unifier env sigma goal;
    match unifier_kind sigma goal with
    | None -> lemmas
    | Some goalUnf -> 
      let lemmaUnfs = List.map (fun (l : CompletionItems.completion_item) -> 
        match (unifier_kind sigma (of_constr l.typ)) with
        | None -> ((Float.min_float), l)
        | Some unf -> 
          let scores = List.map (score_unifier use_um sigma goalUnf) (unpack_unifier unf) in
          let size = size_unifier unf |> Int32.to_float in
          let maxScore = List.fold_left Float.max 0. scores in
          let final = finalScore maxScore size in
          l.debug_info <- (Printf.sprintf "Score: %f, Size: %f, Final Score: %f" maxScore size final);
          (final, l)
      ) lemmas in
      let sorted = List.stable_sort (fun (x, _) (y, _) -> Float.compare x y) lemmaUnfs in
      Printf.eprintf "Best Result:\n";
      debug_print_unifier env sigma (List.nth sorted 0 |> snd |> (fun v -> v.typ)|> of_constr);
      debug_print_kind_of_type sigma env (List.nth sorted 0 |> snd |> (fun v -> v.typ)|> of_constr |> type_kind_opt sigma);
      List.map snd sorted
end

(*Heuristics*)

let rank_choices algorithm = 
  let open Lsp.LspData.Settings.RankingAlgoritm in
  match algorithm with
  | SimpleTypeIntersection -> SimpleAtomics.rank
  | SplitTypeIntersection -> Split.rank
  | StructuredTypeEvaluation -> Structured.rank true
 
let take n l =
  let rec sub_list n accu l =
    match l with 
    | [] -> accu 
    | hd :: tl ->
      if n = 0 then accu 
      else sub_list (n - 1) (hd :: accu) tl
  in
  List.rev (sub_list n [] l)

let get_completion_items ~id params st loc algorithm =
  try 
    let open Yojson.Basic.Util in
    match get_goal_type_option st (Some loc), DocumentManager.get_lemmas st loc with
    | None, _ | _ , None -> Error ("Error in creating completion items")
    | Some (goal, sigma, env), Some lemmas ->
      rank_choices algorithm goal sigma env lemmas
      |> take 10000 
      |> List.map CompletionItems.pp_completion_item 
      |> Result.ok
  with e -> 
    Printf.eprintf "Error in creating completion items: %s" (Printexc.to_string e);
    Error ("Error in creating completion items: " ^ (Printexc.to_string e))
