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

let log = Dm.ParTactic.TacticWorkerProcess.log 

let main_worker options ~opts:_ state =
  let initial_vernac_state = Vernacstate.freeze_full_state () in
  try Dm.ParTactic.TacticWorkerProcess.main ~st:initial_vernac_state options
  with exn ->
    let bt = Printexc.get_backtrace () in
    log Printexc.(to_string exn);
    log bt;
    flush_all ()

let vscoqtop_specific_usage = Boot.Usage.{
  executable_name = "vscoqtop_tactic_worker";
  extra_args = "";
  extra_options = "";
}


let _ =
  Coqinit.init_ocaml ();
  let opts, emoptions = Coqinit.parse_arguments ~parse_extra:Dm.ParTactic.TacticWorkerProcess.parse_options ~usage:vscoqtop_specific_usage () in
  let injections = Coqinit.init_runtime opts in
  Coqinit.start_library ~top:Coqargs.(dirpath_of_top opts.config.logic.toplevel_name) injections;
  log @@ "started";
  Sys.(set_signal sigint Signal_ignore);
  main_worker ~opts emoptions ()
