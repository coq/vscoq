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

(* Note: this queue is not very useful today, as we process results in the main
vscoq process, which does not allow for real asynchronous processing of results. *)
let query_results_queue = Queue.create ()

let query_feedback : notification Sel.Event.t =
  Sel.On.queue query_results_queue (fun x -> QueryResultNotification x)

[%%if coq = "8.18"]
open Vernacexpr
open Pp
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
let adapt_pr_search f r k e c = f r k e (Evd.from_env e) c
[%%else]
let interp_search_restriction = ComSearch.interp_search_restriction
let adapt_pr_search f = f
[%%endif]

let interp_search ~id env sigma s r =
  let pr_search ref _kind env sigma c =
    let pr = pr_global ref in
    let open Impargs in
    let impls = implicits_of_global ref in
    let impargs = select_stronger_impargs impls in
    let impargs = List.map binding_kind_of_status impargs in
    let pc = pr_ltype_env env sigma ~impargs c in
    let name = pp_of_coqpp pr in
    let statement = pp_of_coqpp pc in
    Queue.push { id; name; statement } query_results_queue
  in
  let r = interp_search_restriction r in
  (Search.search env sigma (List.map (ComSearch.interp_search_request env sigma) s) r |>
    Search.prioritize_search) (adapt_pr_search pr_search);
  [query_feedback]
