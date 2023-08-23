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
open Protocol.Printing
open Protocol.LspWrapper
open Vernacexpr
open Pp
(* Note: this queue is not very useful today, as we process results in the main
vscoq process, which does not allow for real asynchronous processing of results. *)
let query_results_queue = Queue.create ()

let query_feedback : notification Sel.Event.t =
  Sel.On.queue query_results_queue (fun x -> QueryResultNotification x)

(* TODO : remove these two functions when interp_search_restriction is 
  added in the comSearch.mli in Coq (they're simply copied here for now) *)
let global_module qid =
    try Nametab.full_name_module qid
    with Not_found ->  
      CErrors.user_err ?loc:qid.CAst.loc
       (str "Module/Section " ++ Ppconstr.pr_qualid qid ++ str " not found.")
let interp_search_restriction = function
  | SearchOutside l -> (List.map global_module l, true)
  | SearchInside l -> (List.map global_module l, false)

let interp_search ~id env sigma s r =
  let pr_search ref _kind env c =
    let name = pr_global ref in
    let open Impargs in
    let impls = implicits_of_global ref in
    let impargs = select_stronger_impargs impls in
    let impargs = List.map binding_kind_of_status impargs in
    let statement = pr_ltype_env env Evd.(from_env env) ~impargs c in
    let name = pp_of_coqpp name in
    let statement = pp_of_coqpp statement in
    Queue.push { id; name; statement } query_results_queue
  in
  let r = interp_search_restriction r in
  (Search.search env sigma (List.map (ComSearch.interp_search_request env Evd.(from_env env)) s) r |>
    Search.prioritize_search) pr_search;
  [query_feedback]
