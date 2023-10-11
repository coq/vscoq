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
open Lsp.Types

type t = {
  text : Lsp.Text_document.t;
  lines : int array; (* locs of beginning of lines *)
}

let compute_lines text_doc =
  let text = Lsp.Text_document.text text_doc in
  let lines = String.split_on_char '\n' text in
  let _,lines_locs = CList.fold_left_map (fun acc s -> let n = String.length s in n + acc + 1, acc) 0 lines in
  Array.of_list lines_locs

let compute_lines_ocaml_lsp text_doc = 
  let text = Lsp.Text_document.text text_doc in
  let lines = String.split_on_char '\n' text in
  let get_line_loc line_number = 
    let pos = Position.{line = line_number; character = 0} in
    Lsp.Text_document.absolute_position text_doc pos 
  in
  let lines_locs = List.init (List.length lines) get_line_loc in
  Array.of_list lines_locs

let compare_lines doc log = 
  let text_doc = doc.text in
  let lines = compute_lines text_doc in
  let lines_ocaml = compute_lines_ocaml_lsp text_doc in
  let i = ref 0 in
  while(!i < Array.length lines) do log @@ Format.sprintf "%i <--> %i\n" lines.(!i) lines_ocaml.(!i); incr(i) done

let create text =
  let text = Lsp.Text_document.make ~position_encoding:`UTF16 text in
  { text; lines = compute_lines_ocaml_lsp text }

let text t = Lsp.Text_document.text t.text

let position_of_loc raw loc =
  let i = ref 0 in
  while (!i < Array.length raw.lines && raw.lines.(!i) <= loc) do incr(i) done;
  Position.{ line = !i - 1; character = loc - raw.lines.(!i - 1) }

let loc_of_position raw Position.{ line; character } =
  raw.lines.(line) + character

let end_loc raw =
  String.length @@ Lsp.Text_document.text raw.text

let range_of_loc raw loc =
  let open Range in
  { start = position_of_loc raw loc.Loc.bp;
    end_ = position_of_loc raw loc.Loc.ep;
  }

let apply_text_edits raw edits = 
  let text_doc = Lsp.Text_document.apply_text_document_edits raw.text edits in
  let new_lines = compute_lines_ocaml_lsp text_doc in
  { text = text_doc; lines = new_lines}

(* let apply_text_edit raw (Range.{start; end_}, editText) =
  let start = loc_of_position raw start in
  let stop = loc_of_position raw end_ in
  let before = String.sub raw.text 0 start in
  let after = String.sub raw.text stop (String.length raw.text - stop) in
  let new_text = before ^ editText ^ after in (* FIXME avoid concatenation *)
  let new_lines = compute_lines new_text in (* FIXME compute this incrementally *)
  { text = new_text; lines = new_lines }, start  *)

let word_at_position raw pos : string option =
  let r = Str.regexp {|\([a-zA-Z_][a-zA-Z_0-9]*\)|} in
  let start = ref (loc_of_position raw pos) in
  let word = ref None in
  let raw_text = Lsp.Text_document.text raw.text in
  while (Str.string_match r raw_text start.contents) do
    start := start.contents - 1;
    word := Some (Str.matched_string raw_text);
  done;
  word.contents

let only_whitespace_between raw loc1 loc2 =
  let res = ref true in
  for i = loc1 to loc2 do
    let raw_text = Lsp.Text_document.text raw.text in
    let code = Char.code raw_text.[i] in
    if code <> 0x20 && code <> 0xD && code <> 0xA && code <> 0x9
      then res := false
  done;
  !res