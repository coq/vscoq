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

let line_text raw i =
  if i + 1 < Array.length raw.lines then
    String.sub raw.text (raw.lines.(i)) (raw.lines.(i+1) - raw.lines.(i))
  else
    String.sub raw.text (raw.lines.(i)) (String.length raw.text - raw.lines.(i))

let get_character_pos linestr loc =
  let rec loop d =
    if Uutf.decoder_byte_count d >= loc then
      Uutf.decoder_count d
    else
      match Uutf.decode d with
      | `Uchar _ -> loop d
      | `Malformed _ -> loop d
      | `End -> Uutf.decoder_count d
      | `Await -> assert false
  in
  let nln = `Readline (Uchar.of_int 0x000A) in
  let encoding = `UTF_8 in
  loop (Uutf.decoder ~nln ~encoding (`String linestr))

let position_of_loc raw loc =
  let i = ref 0 in
  while (!i < Array.length raw.lines && raw.lines.(!i) <= loc) do incr(i) done;
  let line = !i - 1 in
  let char = get_character_pos (line_text raw line) (loc - raw.lines.(line)) in
  Position.{ line = line; character = char }

let get_character_loc linestr pos =
  let rec loop d =
    if Uutf.decoder_count d >= pos then
      Uutf.decoder_byte_count d
    else
      match Uutf.decode d with
      | `Uchar _ -> loop d
      | `Malformed _ -> loop d
      | `End -> Uutf.decoder_byte_count d
      | `Await -> assert false
  in
  let nln = `Readline (Uchar.of_int 0x000A) in
  let encoding = `UTF_8 in
  loop (Uutf.decoder ~nln ~encoding (`String linestr))

let loc_of_position raw Position.{ line; character } =
  let linestr = line_text raw line in
  let charloc = get_character_loc linestr character in
  raw.lines.(line) + charloc

let end_loc raw =
  String.length raw.text

let range_of_loc raw loc =
  let open Range in
  { start = position_of_loc raw loc.Loc.bp;
    end_ = position_of_loc raw loc.Loc.ep;
  }

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