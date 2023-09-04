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

let loop injections =
  let events = LspManager.init injections in
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
    log "==========================================================";
    log @@ Pp.string_of_ppcmds @@ CErrors.iprint_no_report info;
    log "=========================================================="

let vscoqtop_specific_usage = {
  Boot.Usage.executable_name = "vscoqtop";
  extra_args = "";
  extra_options = {|
VSCoq options are:
  -vscoq-d c1,..,cn      enable debugging for vscoq components c1 ... cn.
                         Known components:
                           all (shorthand for all components)
                           init (all components but only during initialization)
|} ^ "\t\t\t   " ^ String.concat "\n\t\t\t   " (Dm.Log.logs ()) ^ {|
  
|}
}

let rec skip_xd acc = function
  | [] -> (), List.rev acc
  | "-vscoq-d" :: _ :: rest -> skip_xd acc rest
  | x :: rest -> skip_xd (x::acc) rest

let _ =
  Coqinit.init_ocaml ();
  log "------------------ begin ---------------";
  let initial_args =
    let cwd = Unix.getcwd () in
    match CoqProject_file.find_project_file ~from:cwd ~projfile_name:"_CoqProject" with
    | None ->
      log (Printf.sprintf "No project file found in %s" cwd);
      Coqargs.default
    | Some f ->
      let project = CoqProject_file.read_project_file ~warning_fn:(fun _ -> ()) f in
      let args = CoqProject_file.coqtop_args_from_project project in
      log (Printf.sprintf "Arguments from project file %s: %s" f (String.concat " " args));
      fst @@ Coqargs.parse_args ~usage:vscoqtop_specific_usage ~init:Coqargs.default args in
  let opts, () = Coqinit.parse_arguments ~usage:vscoqtop_specific_usage ~initial_args ~parse_extra:(fun x -> skip_xd [] x) () in
  let injections = Coqinit.init_runtime opts in
  Safe_typing.allow_delayed_constants := true; (* Needed to delegate or skip proofs *)
  Flags.quiet := true;
  Sys.(set_signal sigint Signal_ignore);
  loop injections
