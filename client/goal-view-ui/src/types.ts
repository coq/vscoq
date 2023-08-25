import { integer } from "vscode-languageclient";
type Nullable<T> = T | null;

export type PpTag = string;

export type BlockType =
  | ["Pp_hbox"]
  | ["Pp_vbox", integer]
  | ["Pp_hvbox", integer]
  | ["Pp_hovbox", integer];

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