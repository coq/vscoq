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

(** This toplevel implements an LSP-based server language for VsCode,
    used by the VsCoq extension. *)

let Dm.Types.Log log = Dm.Log.mk_log "top"

let loop () =
  let events = LspManager.init () in
  let rec loop (todo : LspManager.event Sel.Todo.t) =
    (*log @@ "looking for next step";*)
    flush_all ();
    let ready, todo = Sel.pop todo in
    let nremaining = Sel.Todo.size todo in
    log @@ "Main loop event ready: " ^ Pp.string_of_ppcmds (LspManager.pr_event ready) ^ " , " ^ string_of_int nremaining ^ " events waiting";
    let new_events = LspManager.handle_event ready in
    let todo = Sel.Todo.add todo new_events in
    loop todo
  in
  let todo = Sel.Todo.add Sel.Todo.empty events in
  try loop todo
  with exn ->
    let info = Exninfo.capture exn in
    log ~force:true "==========================================================";
    log ~force:true @@ Pp.string_of_ppcmds @@ CErrors.iprint_no_report info;
    log ~force:true "=========================================================="

[%%if coq = "8.18" || coq = "8.19" || coq = "8.20"]
let _ =
  Coqinit.init_ocaml ();
  log "------------------ begin ---------------";
  let cwd = Unix.getcwd () in
  let opts = Args.get_local_args  cwd in
  let _injections = Coqinit.init_runtime opts in
  Safe_typing.allow_delayed_constants := true; (* Needed to delegate or skip proofs *)
  Sys.(set_signal sigint Signal_ignore);
  loop ()
[%%else]

let () =
  Coqinit.init_ocaml ();
  log "------------------ begin ---------------";
  let cwd = Unix.getcwd () in
  let opts = Args.get_local_args cwd in
  let () = Coqinit.init_runtime ~usage:(Args.usage ()) opts in
  Safe_typing.allow_delayed_constants := true; (* Needed to delegate or skip proofs *)
  Sys.(set_signal sigint Signal_ignore);
  loop ()
[%%endif]
