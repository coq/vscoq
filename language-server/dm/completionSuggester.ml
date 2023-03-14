module CompactedDecl = Context.Compacted.Declaration
open Printer
open EConstr
open Names

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

type unifier = 
  | SortUniType of ESorts.t
  | AtomicUniType of types * unifier array

let unifier_kind sigma (t : types) : unifier = 
  let rec aux bruijn t = match kind sigma t with
    | Sort s -> SortUniType s
    | Cast (c,_,t) -> failwith "Not implemented"
    | Prod (na,t,c) -> aux (aux bruijn t :: bruijn) c 
    | LetIn (na,b,t,c) -> failwith "Not implemented"
    | App (c,l) -> AtomicUniType (c, Array.map (aux bruijn) l)
    | Rel i -> List.nth bruijn (i-1)
    | (Meta _ | Var _ | Evar _ | Const _
    | Proj _ | Case _ | Fix _ | CoFix _ | Ind _)
      -> AtomicUniType (t,[||])
    | (Lambda _ | Construct _ | Int _ | Float _ | Array _) -> failwith "Not a type"
  in
  aux [] t

let debug_print_unifier env sigma t : unit = 
  let rec aux i u =
    Printf.eprintf "%s" (String.init i (fun _ -> ' '));
    match u with
    | SortUniType s -> Printf.eprintf "SortUniType\n";
    | AtomicUniType (t, ua) -> 
      Printf.eprintf "AtomicUniType %s\n" (Pp.string_of_ppcmds (pr_econstr_env env sigma t));
      Array.iter (fun u -> aux (i + 1) u) ua
  in
  aux 0 (unifier_kind sigma t)

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
  Atomics.fold (fun t l -> (Pp.string_of_ppcmds (pr_econstr_env env sigma t ) |> Printf.sprintf "%s") :: l) atomics [] 
  |> String.concat "," 
  |> Printf.eprintf "Atomics: [%s]\n"

let debug_print_decomposed env sigma c =
  let (list, other_c) = decompose_prod sigma c in 
  list
  |> List.map snd 
  |> List.cons other_c
  |> List.map (fun typ -> typ |> pr_econstr_env env sigma |> Pp.string_of_ppcmds) 
  |> List.rev
  |> String.concat "; " 
  |> Printf.eprintf "[%s]\n"

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

let compare_types (goal : Atomics.t) (sigma: Evd.evar_map) (a1, _ : types * _) (a2, _ : types * _) : int = 
  let a1_best = best_subtype sigma goal a1 in
  let a2_best = best_subtype sigma goal a2 in
  match (Atomics.inter a1_best goal, Atomics.inter a2_best goal) with
  | r1, r2 when Atomics.cardinal r1 = Atomics.cardinal r2 -> 
    (* If the size is equal, priotize the one with fewest types *)
    compare (Atomics.cardinal (atomic_types sigma a1)) (Atomics.cardinal (atomic_types sigma a2))
  | r1, r2 -> 
    (* Return the set with largest overlap, so we sort in increasing order swap the arguments *)
    compare (Atomics.cardinal r2) (Atomics.cardinal r1)


let rank_split_type_intersection (goal : Evd.econstr) sigma env lemmas : CompletionItems.completion_item list =
  (*Split type intersection: Split the lemmas by implications, compare the suffix to the goal, pick best match*)
  let lemmaTypes = List.map (fun (l : CompletionItems.completion_item) -> 
    (of_constr l.typ, l)
  ) lemmas in
  let goalAtomics = atomic_types sigma goal in
  List.stable_sort (compare_types goalAtomics sigma) lemmaTypes |> 
  List.map snd

(*Put the chosen heuristic on the line below*)
let rank_choices = rank_split_type_intersection

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
  let open Yojson.Basic.Util in
  let hypotheses = get_hyps st loc in
  let lemmasOption = DocumentManager.get_lemmas st loc in
  let result = get_goal_type_option st (Some loc)
  |> Option.map (fun (goal, sigma, env) -> 
    let lemmas = lemmasOption |> Option.map 
      (fun l -> 
        rank_choices goal sigma env l 
        |> take 10000 
        |> List.map CompletionItems.pp_completion_item
      ) in
    [lemmas; hypotheses] 
    |> List.map (Option.default []) 
    |> List.flatten
  ) 
  |> Option.default [] in
  if result = [] then Printf.eprintf "No results\n";
  result
