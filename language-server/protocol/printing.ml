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

let rec pp_of_coqpp t = match Pp.repr t with
  | Pp.Ppcmd_empty -> Ppcmd_empty
  | Pp.Ppcmd_string s -> Ppcmd_string s
  | Pp.Ppcmd_glue l -> Ppcmd_glue (List.map pp_of_coqpp l)
  | Pp.Ppcmd_box (bt, pp) -> Ppcmd_box (bt, pp_of_coqpp pp)
  | Pp.Ppcmd_tag (tag, pp) -> Ppcmd_tag (tag, pp_of_coqpp pp)
  | Pp.Ppcmd_print_break (m,n) -> Ppcmd_print_break (m,n)
  | Pp.Ppcmd_force_newline -> Ppcmd_force_newline
  | Pp.Ppcmd_comment l -> Ppcmd_comment l