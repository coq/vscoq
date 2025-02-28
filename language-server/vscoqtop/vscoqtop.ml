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

let Misc.Log.Log log = Misc.Log.mk_log "top"

let loop () =
  let events = LspManager.init () in
  let rec loop (todo : LspManager.event Sel.Todo.t) =
    (*log fun () -> "looking for next step";*)
    flush_all ();
    let ready, todo = Sel.pop todo in
    let nremaining = Sel.Todo.size todo in
    log (fun () -> "Main loop event ready: " ^ (LspManager.pr_event ready) ^ " , " ^ string_of_int nremaining ^ " events waiting");
    let new_events = LspManager.handle_event ready in
    let todo = Sel.Todo.add todo new_events in
    loop todo
  in
  let todo = Sel.Todo.add Sel.Todo.empty events in
  try loop todo
  with exn ->
    let info = Exninfo.capture exn in
    log ~force:true (fun () -> "==========================================================");
    log ~force:true (fun () -> Pp.string_of_ppcmds @@ CErrors.iprint_no_report info);
    log ~force:true (fun () -> "==========================================================")

let () =
  log (fun () -> "------------------ begin ---------------");
  let cwd = Unix.getcwd () in
  let opts = Args.get_local_args cwd in
  Rocq_worker.API.init ~usage:(Args.usage ()) opts;
  loop ()