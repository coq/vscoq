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

type pp_tag = string [@@deriving yojson]

type block_type = Pp.block_type =
  | Pp_hbox
  | Pp_vbox   of int
  | Pp_hvbox  of int
  | Pp_hovbox of int
[@@deriving yojson]

type pp =
| Ppcmd_empty
| Ppcmd_string of string
| Ppcmd_glue of pp list
| Ppcmd_box  of block_type * pp
| Ppcmd_tag of pp_tag * pp
| Ppcmd_print_break of int * int
| Ppcmd_force_newline
| Ppcmd_comment of string list
[@@deriving yojson]

let rec regroup_tags_aux acc = function
  | [] -> acc
  | hd :: tl ->
    match Pp.repr hd with
    | Pp.Ppcmd_glue l ->
      let acc = regroup_tags_aux acc l in
      regroup_tags_aux acc tl
    | Pp.Ppcmd_tag (s, pp) when String.starts_with ~prefix:Pp.start_pfx s ->
      let pp = regroup_tags [pp] in
      regroup_tags_aux (pp::acc) tl
    | Pp.Ppcmd_tag (s, pp) when String.starts_with ~prefix:Pp.end_pfx s ->
      let pp = regroup_tags [pp] in
      let n = String.length Pp.end_pfx in
      let tag = String.sub s n (String.length s - n) in
      begin match acc with
      | acc0::acc1::tlacc ->
        let acc1 = Pp.tag tag (Pp.seq ((List.rev acc0) @ pp)) :: acc1 in
        regroup_tags_aux (acc1 :: tlacc) tl
      | _ -> failwith ("extra closing tag: " ^ tag)
      end
    | _ ->
      let acc = (hd::List.hd acc)::List.tl acc in
      regroup_tags_aux acc tl

and regroup_tags l =
 match regroup_tags_aux [[]] l with [l] -> List.rev l | _ -> failwith "tag not closed"

let rec pp_of_coqpp t = match Pp.repr t with
  | Pp.Ppcmd_empty -> Ppcmd_empty
  | Pp.Ppcmd_string s -> Ppcmd_string s
  | Pp.Ppcmd_glue l -> (* We are working around a Coq hack here *)
    let l = regroup_tags l in
    Ppcmd_glue (List.map pp_of_coqpp l)
  | Pp.Ppcmd_box (bt, pp) -> Ppcmd_box (bt, pp_of_coqpp pp)
  | Pp.Ppcmd_tag (tag, pp) -> Ppcmd_tag (tag, pp_of_coqpp pp)
  | Pp.Ppcmd_print_break (m,n) -> Ppcmd_print_break (m,n)
  | Pp.Ppcmd_force_newline -> Ppcmd_force_newline
  | Pp.Ppcmd_comment l -> Ppcmd_comment l