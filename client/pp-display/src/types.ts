import { integer } from "vscode-languageclient";
export type PpTag = string;

export enum PpMode {
    horizontal = "Pp_hbox",
    vertical = "Pp_vbox",
    hvBox = "Pp_hvbox",
    hovBox = "Pp_hovbox"
}

export type BlockType =
  | [PpMode.horizontal]
  | [PpMode.vertical, integer]
  | [PpMode.hvBox, integer]
  | [PpMode.hovBox, integer];

export type PpBox = ["Ppcmd_box", BlockType, PpString];

export type PpString =
  | ["Ppcmd_empty"]
  | ["Ppcmd_string", string]
  | ["Ppcmd_glue", PpString[]]
  | ["Ppcmd_box", BlockType, PpString]
  | ["Ppcmd_tag", PpTag, PpString]
  | ["Ppcmd_print_break", integer, integer]
  | ["Ppcmd_force_newline"]
  | ["Ppcmd_comment", string[]];

export type FlattenedPpString =
  | ["Ppcmd_empty"]
  | ["Ppcmd_string", string]
  | ["Ppcmd_box", BlockType, PpString[]]
  | ["Ppcmd_tag", PpTag, PpString]
  | ["Ppcmd_print_break", integer, integer]
  | ["Ppcmd_force_newline"]
  | ["Ppcmd_comment", string[]];

export enum DisplayType {
    box = "box",
    term = "term",
    break = "break"
}

export type BreakInfo = {
    id: string,
    offset: number
};

export interface Break {
    id: string,
    type: DisplayType.break,
    offset: number,
    mode: PpMode,
    horizontalIndent: number, 
    indent: number,
    shouldBreak: boolean,
}

export interface Term {
    type: DisplayType.term,
    classList:  string[],
    content: string,
}

export type BoxDisplay = Break | Term | Box | null;

export interface Box {
    id: string,
    type: DisplayType.box,
    depth: number,
    classList: string[],
    mode: PpMode,
    indent: number,
    boxChildren: BoxDisplay[]
}