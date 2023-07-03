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
open Protocol.LspWrapper

val query_feedback : notification Sel.Event.t

val interp_search :
  id:string ->
  Environ.env ->
  Evd.evar_map ->
  (bool * Vernacexpr.search_request) list ->
  Vernacexpr.search_restriction ->
  notification Sel.Event.t list
