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

open Ppx_yojson_conv_lib.Yojson_conv.Primitives

type pp_tag = string [@@deriving yojson]

type block_type =
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

