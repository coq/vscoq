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
open Lsp
open LspData

type text_edit = Range.t * string

type t = {
  text : string;
  lines : int array; (* locs of beginning of lines *)
}

let compute_lines text =
  let lines = String.split_on_char '\n' text in
  let _,lines_locs = CList.fold_left_map (fun acc s -> let n = String.length s in n + acc + 1, acc) 0 lines in
  Array.of_list lines_locs

let create text = { text; lines = compute_lines text }

let text t = t.text

let position_of_loc raw loc =
  let i = ref 0 in
  while (!i < Array.length raw.lines && raw.lines.(!i) <= loc) do incr(i) done;
  Position.{ line = !i - 1; character = loc - raw.lines.(!i - 1) }

let loc_of_position raw Position.{ line; character } =
  raw.lines.(line) + character

let end_loc raw =
  String.length raw.text

let range_of_loc raw loc =
  let open Range in
  { start = position_of_loc raw loc.Loc.bp;
    end_ = position_of_loc raw loc.Loc.ep;
  }

let previous_white_space raw pos =
  let r = Str.regexp "[ \n\r\x0c\t]" in
  let start = ref (loc_of_position raw pos - 1) in
  while (start.contents >= 0) && not (Str.string_match r raw.text start.contents) do
    start := start.contents - 1;
  done;
  if (start.contents < 0) then None else
    (Printf.eprintf "space-character: {%c}\n" (String.get raw.text start.contents);
    Some (start.contents))

let previous_non_white_space raw pos =
  let r = Str.regexp "[ \n\r\x0c\t]" in
  let start = ref (loc_of_position raw pos - 1) in
  while (start.contents >= 0) && Str.string_match r raw.text start.contents do
    start := start.contents - 1;
  done;
  if (start.contents < 0) then None else
    (Printf.eprintf "non-space-character: {%c}\n" (String.get raw.text start.contents);
    Some (start.contents))

let previous_word raw pos : string option =
  Printf.eprintf "character at loc: {%s}\n" (String.sub raw.text (loc_of_position raw pos) 1);
  let a = previous_white_space raw pos in
  let endo = Option.bind a (fun x -> previous_non_white_space raw (position_of_loc raw x)) in
  Option.bind endo (fun endi -> 
    let start = previous_white_space raw (position_of_loc raw endi) in 
    Option.map (fun starti -> 
      Printf.eprintf "starti: %d, endi: %d, prevSpace: %d, loc: %d\n" starti endi (Option.get a) (loc_of_position raw pos);
      String.sub raw.text (starti + 1) (endi - starti)
      ) start) 


let word_at_position raw pos : string option =
  let r = Str.regexp {|\([a-zA-Z_][a-zA-Z_0-9]*\)|} in
  let start = ref (loc_of_position raw pos) in
  let word = ref None in
  while (Str.string_match r raw.text start.contents) do
    start := start.contents - 1;
    word := Some (Str.matched_string raw.text);
  done;
  word.contents

let apply_text_edit raw (Range.{start; end_}, editText) =
  let start = loc_of_position raw start in
  let stop = loc_of_position raw end_ in
  let before = String.sub raw.text 0 start in
  let after = String.sub raw.text stop (String.length raw.text - stop) in
  let new_text = before ^ editText ^ after in (* FIXME avoid concatenation *)
  let new_lines = compute_lines new_text in (* FIXME compute this incrementally *)
  { text = new_text; lines = new_lines }, start

let only_whitespace_between raw loc1 loc2 =
  let res = ref true in
  for i = loc1 to loc2 do
    let code = Char.code raw.text.[i] in
    if code <> 0x20 && code <> 0xD && code <> 0xA && code <> 0x9
      then res := false
  done;
  !res