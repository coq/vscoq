import { integer } from "vscode-languageclient";
type Nullable<T> = T | null;

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

export type PpString =
  | ["Ppcmd_empty"]
  | ["Ppcmd_string", string]
  | ["Ppcmd_glue", PpString[]]
  | ["Ppcmd_box", BlockType, PpString]
  | ["Ppcmd_tag", PpTag, PpString]
  | ["Ppcmd_print_break", integer, integer]
  | ["Ppcmd_force_newline"]
  | ["Ppcmd_comment", string[]];

export type Hyp = PpString;

export type FlattenedPpString =
  | ["Ppcmd_empty"]
  | ["Ppcmd_string", string]
  | ["Ppcmd_box", BlockType, PpString[]]
  | ["Ppcmd_tag", PpTag, PpString]
  | ["Ppcmd_print_break", integer, integer]
  | ["Ppcmd_force_newline"]
  | ["Ppcmd_comment", string[]];

export interface Goal {
    id: string,
    goal: PpString, 
    hypotheses: Hyp[],
};

export interface CollapsibleGoal extends Goal  {
    isOpen: boolean;
};

export type ProofViewGoalsType = {
    main: CollapsibleGoal[];
    shelved: CollapsibleGoal[];
    givenUp: CollapsibleGoal[];
};

export enum ProofViewGoalsKey {
    main = "main", 
    shelved = "shelved", 
    givenUp = "givenUp"
}

export enum MessageSeverity {
    error = 1, 
    warning,
    information,
    hint
}

export type ProofViewMessage = [MessageSeverity, PpString];

export type GoalArray = Goal[];

export type GoalArrayOrNull = Nullable<Goal[]>;

export type ProofViewGoals = Nullable<ProofViewGoalsType>;