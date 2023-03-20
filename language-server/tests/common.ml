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

open Dm
open Base
open Types

let injections =
  Coqinit.init_ocaml ();
  let opts, _ = Coqargs.parse_args
    ~usage:(Boot.Usage.{executable_name = ""; extra_args = ""; extra_options = ""})
    ~init:Coqargs.default ["";"-coqlib";Unix.getcwd ()^"/../../install/default/lib/coq"] in
  Coqinit.init_runtime opts

let init_state = Vernacstate.freeze_full_state ~marshallable:false

let openDoc ~uri ~text =
  DocumentManager.init init_state ~opts:injections ~uri ~text


let run r =
  [%test_pred: (_,string) Result.t ] (function Error _ -> false | _ -> true) r;
  match r with
  | Ok x -> x
  | Error _ -> assert false
  
type simple_sentence = {
  start : int;
  stop : int;
  id : sentence_id;
}

let ss_of_s ({ start; stop; id; _ } : Document.sentence) : simple_sentence =
   { start; stop; id }

type _ parse =
  | P : 'a parse -> (simple_sentence * 'a) parse
  | E : 'a parse -> (simple_sentence * 'a) parse
  | O : unit parse
  
let rec parse : type a. int -> Document.sentence list -> a parse -> (a,string) Result.t =
  let open Document in
  let open Result in
  fun n l spec ->
    match spec, l with
    | O, [] -> Ok ()
    | P spec, ({ id; ast = ValidAst _ } as s) :: l ->
        parse (n+1) l spec >>= (fun a -> Ok(ss_of_s s,a))
    | E spec, ({ id; ast = ParseError _ } as s) :: l ->
        parse (n+1) l spec >>= (fun a -> Ok(ss_of_s s ,a))
    | O, l -> Error ("more sentences than expected, extra " ^ Int.to_string (List.length l))
    | P _, [] -> Error ("less sentences than expected, only " ^ Int.to_string n)
    | E _, [] -> Error ("less sentences than expected, only " ^ Int.to_string n)
    | P _, _ :: _ -> Error ("unexpected parse error at sentence number " ^ Int.to_string n)
    | E _, _ :: _ -> Error ("missing parse error at sentence number " ^ Int.to_string n)

    
let d_sentences doc spec = 
  let sentences = Document.sentences_sorted_by_loc doc in
  let r = run (parse 0 sentences spec) in
  r

let dm_parse st spec =
  let st = DocumentManager.validate_document st in
  let doc = DocumentManager.Internal.document st in
  st, d_sentences doc spec

let sentence_id_of_sexp s = Stateid.of_int (Sexplib.Std.int_of_sexp s)
let sexp_of_sentence_id i = Sexplib.Std.sexp_of_int (Stateid.to_int i)

let compare_sentence_id = Stateid.compare

type (_,'a) count =
  | O : (unit,'a) count
  | S : ('c,'a) count -> ('a * 'c, 'a) count

let rec count : type a b. int -> b list -> (a,b) count -> (a,string) Result.t =
  let open Result in
  fun n l spec ->
    match spec, l with
    | O, [] -> Ok ()
    | S spec, x :: l ->
      count (n+1) l spec >>= (fun a -> Ok(x,a))
    | O, l -> Error ("more items than expected, extra " ^ Int.to_string (List.length l))
    | S _, [] -> Error ("less items than expected, only " ^ Int.to_string n)
let count l spec = count 0 l spec

type _ task_approx =
  | Exec : sentence_id task_approx
  | Skip : sentence_id task_approx
  | Query : sentence_id task_approx
  | Proof : ('a,sentence_id) count -> (sentence_id * 'a * sentence_id) task_approx

let task : type a. Scheduler.task -> a task_approx -> (a,string) Result.t =
  let open Result in
  fun t spec ->
    match spec, t with
    | Exec, Exec { id } -> Ok id
    | Skip, Skip id -> Ok id
    | Query, Query { id } -> Ok id
    | Proof c, OpaqueProof { tasks; opener_id; terminator } ->
        count (List.map ~f:(fun x -> x.id) tasks) c >>= (fun l ->
        Ok (opener_id,l,terminator.id))
    | _, Skip _ -> Error "unexpected Skip"
    | _, Query _ -> Error "unexpected Query"
    | _, Exec _ -> Error "unexpected Exec"
    | _, OpaqueProof _ -> Error "unexpected OpaqueProof"


let task st id spec =
  let sch = Document.schedule (DocumentManager.Internal.document st) in
  let init, t = Scheduler.task_for_sentence sch id in
  init, run (task t spec)
