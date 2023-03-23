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

open Types

val mk_log : string -> (string -> unit) log
val logs : unit -> string list

type event
type events = event Sel.event list

val lsp_initialization_done : unit -> events
val handle_event : event -> unit

val worker_initialization_begins : unit -> unit
val worker_initialization_done : fwd_event:(event -> unit) -> unit
  