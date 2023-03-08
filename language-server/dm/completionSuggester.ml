module CompactedDecl = Context.Compacted.Declaration
open Printer
open EConstr
open Names

type unifier = 
  | SortUniType of ESorts.t
  | AtomicUniType of types * unifier array

module TypeCompare = struct
  type t = types
  let compare = compare
end

module Atomics = Set.Make(TypeCompare)

let mk_hyp sigma d (env,l) =
  let d' = CompactedDecl.to_named_context d in
  let env' = List.fold_right Environ.push_named d' env in
  let ids, typ = match d with
  | CompactedDecl.LocalAssum (ids, typ) -> ids, typ
  | CompactedDecl.LocalDef (ids,c,typ) -> ids, typ
  in
  let ids' = List.map (fun id -> Names.Id.to_string id.Context.binder_name) ids in
  let typ' = pr_ltype_env env sigma typ in
  let hyps = ids' |> List.map (fun id -> (id, Pp.string_of_ppcmds typ', "")) in
  (env', hyps @ l)

let get_goal_type st loc =
  let goal, sigma = 
    match DocumentManager.get_proof st loc with
    | Some Proof.{ goals; sigma; _ } -> List.nth goals 0, sigma
    | None -> raise (Invalid_argument "goal") 
  in
  let evi = Evd.find_undefined sigma goal in
  let env = Evd.evar_filtered_env (Global.env ()) evi in
  (Evd.evar_concl evi, sigma, env)

(* This is extremely slow, we should not convert it to a list. *)
let filter_options a = 
  a |> Array.to_list |> Option.List.flatten |> Array.of_list

let unifier_kind sigma (t : types) : unifier option = 
  let rec aux bruijn t = match kind sigma t with
    | Sort s -> SortUniType s |> Option.make
    | Cast (c,_,t) -> failwith "Not implemented"
    | Prod (na,t,c) -> aux (aux bruijn t :: bruijn) c
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

let print_unifier env sigma u =
  let rec aux i u =
    Printf.eprintf "%s" (String.init i (fun _ -> ' '));
    match u with
    | SortUniType s -> Printf.eprintf "SortUniType: ";
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
  aux 0 u

(* AtomicUniType matching should give a better score *)
(* SortUniType in the Goal should only match if they are equal i think. *)
let score_unifier evd (goal : unifier) (u : unifier) : float =
  let rec aux g u : float = match (g, u) with
    | SortUniType s1, SortUniType s2 -> if ESorts.equal evd s1 s2 then 1. else 0.
    (* We might want to check if the t in AtomicUniType actually belongs in the sort*)
    | SortUniType _, _ -> 0. (* If the goal has a sort then it has to match *)
    | _, SortUniType _ -> 1.
    | AtomicUniType (t1, ua1), AtomicUniType (t2, ua2) -> 
      let c = EConstr.compare_constr evd (EConstr.eq_constr evd) t1 t2 |> Bool.to_float in
      if Array.length ua1 <> Array.length ua2 then c
      else (Float.add) c (Array.map2 aux ua1 ua2 |> Array.fold_left (Float.add) 0.)
  in
  aux goal u

let unpack_unifier u : unifier list = 
  let res = ref [] in
  let rec aux u = match u with
    | SortUniType s -> ();
    | AtomicUniType (t, ua) -> 
      res := u :: !res;
      Array.iter aux ua
  in
  aux u;
  !res

let size_unifier u = 
  let rec aux u = match u with
    | SortUniType s -> 1l
    | AtomicUniType (t, ua) -> Array.fold_left (fun acc u -> Int32.add acc (aux u)) 1l ua
  in
  aux u

let debug_print_unifier env sigma t : unit = 
  match (unifier_kind sigma t) with
  | None -> Printf.eprintf "None\n"
  | Some unf ->  List.iter (fun u -> Printf.eprintf "Size: %d\n" (size_unifier u |> Int32.to_int);print_unifier env sigma u) (unpack_unifier unf);
  

type type_kind =
  | SortType   of ESorts.t
  | CastType   of types * types
  | ProdType   of Name.t Context.binder_annot * types * types
  | LetInType  of Name.t Context.binder_annot * types * types * types
  | AtomicType of types * types array

let type_kind sigma t : type_kind = match kind sigma t with
  | Sort s -> SortType s
  | Cast (c,_,t) -> CastType (c, t)
  | Prod (na,t,c) -> ProdType (na, t, c)
  | LetIn (na,b,t,c) -> LetInType (na, b, t, c)
  | App (c,l) -> AtomicType (c, l)
  | (Rel _ | Meta _ | Var _ | Evar _ | Const _
  | Proj _ | Case _ | Fix _ | CoFix _ | Ind _)
    -> AtomicType (t,[||])
  | (Lambda _ | Construct _ | Int _ | Float _ | Array _) -> failwith "Not a type"

let type_kind_opt sigma t = try Some (type_kind sigma t) with exn -> None 

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

(* Currently atomic type also returns "_UNBOUND_REL_N, we should probably skip those. "*)

let atomic_types sigma env t: Atomics.t = 
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


let finalScore score size = Float.sub size (Float.mul score 5.) 
(* Lower is better *)
(* The 5 value is just a placeholder and has not been beenchmarked *)

let compare_atomics (goal : Atomics.t) (a1, _ : Atomics.t * _) (a2, _ : Atomics.t * _) : int = 
  match (Atomics.inter a1 goal, Atomics.inter a2 goal) with
  | r1, r2 when Atomics.cardinal r1 = Atomics.cardinal r2 -> 
    (* If the size is equal, priotize the one with fewest types *)
    compare (Atomics.cardinal a1) (Atomics.cardinal a2)
  | r1, r2 -> 
    (* Return the set with largest overlap, so we sort in increasing order swap the arguments *)
    compare (Atomics.cardinal r2) (Atomics.cardinal r1)

let rank_choices_unf (goal : Evd.econstr) sigma env lemmas : CompletionItems.completion_item list =
  match unifier_kind sigma goal with
  | None -> lemmas
  | Some goalUnf -> 
    let lemmaUnfs = List.map (fun (l : CompletionItems.completion_item) -> 
      match (unifier_kind sigma (of_constr l.typ)) with
      | None -> ((Float.min_float), l)
      | Some unf -> 
        let scores = List.map (score_unifier sigma goalUnf) (unpack_unifier unf) in
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

let rank_choices (goal : Evd.econstr) sigma env lemmas : CompletionItems.completion_item list =
  let lemmaAtomics = List.map (fun (l : CompletionItems.completion_item) -> 
    (atomic_types sigma env (of_constr l.typ), l)
  ) lemmas in
  let goalAtomics = atomic_types sigma env goal in
  List.stable_sort (compare_atomics goalAtomics) lemmaAtomics |> 
  List.map snd

let get_hyps st loc =
  let mk_hyps sigma goal =
    let EvarInfo evi = Evd.find sigma goal in
    let env = Evd.evar_filtered_env (Global.env ()) evi in
    let min_env = Environ.reset_context env in
    let (_env, hyps) =
      Context.Compacted.fold (mk_hyp sigma)
        (Termops.compact_named_context (Environ.named_context env)) ~init:(min_env,[]) in
    hyps in

  DocumentManager.get_proof st (Some loc)
    |> Option.map (fun Proof.{ goals; sigma; _ } -> Option.cata (mk_hyps sigma) [] (List.nth_opt goals 0)) 
 
let take n l =
  let rec sub_list n accu l =
    match l with 
    | [] -> accu 
    | hd :: tl ->
      if n = 0 then accu 
      else sub_list (n - 1) (hd :: accu) tl
  in
  List.rev (sub_list n [] l)

let get_completion_items ~id params st loc =
  try 
    let open Yojson.Basic.Util in
    let lemmasOption = DocumentManager.get_lemmas st loc in
    let goal, sigma, env = get_goal_type st (Some loc) in
    Printf.eprintf "Goal\n:";
    debug_print_unifier env sigma goal;
    let lemmas = lemmasOption |> Option.map 
      (fun l -> 
        rank_choices_unf goal sigma env l |> 
        take 10000 |> 
        List.map CompletionItems.pp_completion_item
      ) in
    lemmas
    |> function 
    | Some l -> Result.Ok l
    | None -> Error ("Error in creating completion items")
  with e -> 
    Printf.eprintf "Error in creating completion items: %s" (Printexc.to_string e);
    Error ("Error in creating completion items: " ^ (Printexc.to_string e))