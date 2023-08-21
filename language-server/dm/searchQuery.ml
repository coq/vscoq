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
open Util
open Printer
open Protocol.LspWrapper

(* Note: this queue is not very useful today, as we process results in the main
vscoq process, which does not allow for real asynchronous processing of results. *)
let query_results_queue = Queue.create ()

let query_feedback : notification Sel.event =
  Sel.on_queue query_results_queue (fun x -> QueryResultNotification x)
  |> Sel.uncancellable

let interp_search ~id env sigma s r =
  let pr_search ref _kind env c =
    let pr = pr_global ref in
    let open Impargs in
    let impls = implicits_of_global ref in
    let impargs = select_stronger_impargs impls in
    let impargs = List.map binding_kind_of_status impargs in
    let pc = pr_ltype_env env Evd.(from_env env) ~impargs c in
    let name = Pp.string_of_ppcmds pr in
    let statement = Pp.string_of_ppcmds pc in
    Queue.push { id; name; statement } query_results_queue
  in
  let r = ComSearch.interp_search_restriction r in
  (Search.search env sigma (List.map (ComSearch.interp_search_request env Evd.(from_env env)) s) r |>
    Search.prioritize_search) pr_search;
  [query_feedback]
