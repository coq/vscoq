(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This toplevel implements an LSP-based server language for VsCode,
    used by the VsCoq extension. *)

let top_debug = CDebug.create ~name:"vscoq.top" ()
let log msg = top_debug Pp.(fun () ->
  str @@ Format.asprintf "              [%d] %s" (Unix.getpid ()) msg)

let loop injections =
  LspManager.init injections;
  let rec loop (events : LspManager.events) =
    log @@ "looking for next step";
    flush_all ();
    let (ready, remaining) = Sel.wait events in
    let nremaining = List.length remaining in
    log @@ "Main loop events ready: " ^ Pp.string_of_ppcmds Pp.(prlist_with_sep spc LspManager.pr_event ready) ^ " , " ^ string_of_int nremaining ^ " events waiting";
    loop (remaining @ CList.map_append LspManager.handle_event ready)
  in
  try loop [LspManager.lsp]
  with exn ->
    let info = Exninfo.capture exn in
    Feedback.msg_debug @@ Pp.str "==========================================================";
    Feedback.msg_debug @@ CErrors.iprint_no_report info;
    Feedback.msg_debug @@ Pp.str "==========================================================";
;;

let vscoqtop_specific_usage = {
  Boot.Usage.executable_name = "vscoqtop";
  extra_args = "";
  extra_options = "";
}

let _ =
  Coqinit.init_ocaml ();
  let initialization_feeder = Feedback.add_feeder (fun fb ->
    match fb.Feedback.contents with
    | Feedback.Message(_,_,msg) -> Printf.eprintf "%s\n" (Pp.string_of_ppcmds msg)
    | _ -> ()
  ) in
  let initial_args =
    match CoqProject_file.find_project_file ~from:(Unix.getcwd ()) ~projfile_name:"_CoqProject" with
    | None -> Coqargs.default
    | Some f ->
      let project = CoqProject_file.read_project_file ~warning_fn:(fun _ -> ()) f in
      let args = CoqProject_file.coqtop_args_from_project project in
      log @@ "Args from project file: " ^ String.concat " " args;
      fst @@ Coqargs.parse_args ~usage:vscoqtop_specific_usage ~init:Coqargs.default args in
  let opts, () = Coqinit.parse_arguments ~usage:vscoqtop_specific_usage ~initial_args ~parse_extra:(fun x -> (), x) () in
  let injections = Coqinit.init_runtime opts in
  Flags.quiet := true;
  Sys.(set_signal sigint Signal_ignore);
  Exninfo.record_backtrace true;
  Feedback.del_feeder initialization_feeder;
  loop injections
