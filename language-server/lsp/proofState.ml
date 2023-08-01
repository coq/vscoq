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
type hyp = {
  identifiers: string list;
  type_ : string; [@key "type"]
  diff: string;
  body: string option; [@yojson.option]
} [@@deriving yojson]

type goal = {
  id: int;
  hypotheses: hyp list;
  goal: string;
} [@@deriving yojson]

type t = {
  goals: goal list;
  shelvedGoals: goal list;
  givenUpGoals: goal list;
} [@@deriving yojson]

open Printer
module CompactedDecl = Context.Compacted.Declaration

let mk_goal env sigma g =
  let EvarInfo evi = Evd.find sigma g in
  let env = Evd.evar_filtered_env env evi in
  let min_env = Environ.reset_context env in
  let id = Evar.repr g in
  let concl = match Evd.evar_body evi with
  | Evar_empty -> Evd.evar_concl evi
  | Evar_defined body -> Retyping.get_type_of env sigma body
  in
  let ccl =
    pr_letype_env ~goal_concl_style:true env sigma concl
  in
  let mk_hyp d (env,l) =
    let d' = CompactedDecl.to_named_context d in
    let env' = List.fold_right EConstr.push_named d' env in
    let ids, body, typ = match d with
    | CompactedDecl.LocalAssum (ids, typ) ->
       ids, None, typ
    | CompactedDecl.LocalDef (ids,c,typ) ->
      ids, Some c, typ
    in
  let ids = List.map (fun id -> (Names.Id.to_string id.Context.binder_name)) ids in
  let typ = pr_letype_env env sigma typ in
    let hyp = {
      identifiers = ids;
      type_ = Pp.string_of_ppcmds typ;
      diff = "None";
      body = Option.map (fun body -> Pp.string_of_ppcmds @@ pr_leconstr_env ~inctx:true env sigma body) body;
    } in
    (env', hyp :: l)
  in
  let (_env, hyps) =
    Context.Compacted.fold mk_hyp
      (Termops.compact_named_context sigma (EConstr.named_context env)) ~init:(min_env,[]) in
  {
    id;
    hypotheses = List.rev hyps;
    goal = Pp.string_of_ppcmds ccl;
  }

  let get_proof st =
    Vernacstate.unfreeze_full_state st;
    match st.interp.lemmas with
    | None -> None
    | Some lemmas ->
      let proof = Proof.data (lemmas |> Vernacstate.LemmaStack.with_top ~f:Declare.Proof.get) in
      let env = Global.env () in
      let sigma = proof.sigma in
      let goals = List.map (mk_goal env sigma) proof.goals in
      let shelvedGoals = List.map (mk_goal env sigma) (Evd.shelf sigma) in
      let givenUpGoals = List.map (mk_goal env sigma) (Evar.Set.elements @@ Evd.given_up sigma) in
      Some {
        goals;
        shelvedGoals;
        givenUpGoals;
      }