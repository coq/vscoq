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
open LspData
open Printer
module CompactedDecl = Context.Compacted.Declaration

let mk_goal sigma g =
  let evi = Evd.find sigma g in
  let env = Evd.evar_filtered_env (Global.env ()) evi in
  let min_env = Environ.reset_context env in
  let id = Evar.repr g in
  let ccl =
    pr_letype_env ~goal_concl_style:true env sigma (Evd.evar_concl evi)
  in
  let mk_hyp d (env,l) =
    let d' = CompactedDecl.to_named_context d in
    let env' = List.fold_right Environ.push_named d' env in
    let ids, body, typ = match d with
    | CompactedDecl.LocalAssum (ids, typ) ->
       ids, None, typ
    | CompactedDecl.LocalDef (ids,c,typ) ->
      ids, Some c, typ
    in
  let ids = List.map (fun id -> `String (Names.Id.to_string id.Context.binder_name)) ids in
  let typ = pr_ltype_env env sigma typ in
    let hyp = `Assoc ([
      "identifiers", `List ids;
      "type", `String (Pp.string_of_ppcmds typ);
      "diff", `String "None";
    ] @ Option.cata (fun body -> ["body", `String (Pp.string_of_ppcmds @@ pr_lconstr_env ~inctx:true env sigma body)]) [] body) in
    (env', hyp :: l)
  in
  let (_env, hyps) =
    Context.Compacted.fold mk_hyp
      (Termops.compact_named_context (Environ.named_context env)) ~init:(min_env,[]) in
  `Assoc [
    "id", `Int id;
    "hypotheses", `List (List.rev hyps);
    "goal", `String (Pp.string_of_ppcmds ccl)
  ]

  let mk_proofview Proof.{ goals; sigma; _ } =
    let goals = List.map (mk_goal sigma) goals in
    let shelved = List.map (mk_goal sigma) (Evd.shelf sigma) in
    let given_up = List.map (mk_goal sigma) (Evar.Set.elements @@ Evd.given_up sigma) in
    `Assoc [
      "type", `String "proof-view";
      "goals", `List goals;
      "shelvedGoals", `List shelved;
      "givenUpGoals", `List given_up
    ]
  
