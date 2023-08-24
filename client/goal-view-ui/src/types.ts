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

export interface DisplayedGoal extends Goal  {
    displayId: number; 
    isOpen: boolean;
};

export type ProofViewType = {
    goals: DisplayedGoal[];
    shelvedGoals: DisplayedGoal[];
    givenUpGoals: DisplayedGoal[];
};

export enum ProofViewKey {
    goals = "goals", 
    shelved = "shelvedGoals", 
    givenUp = "givenUpGoals"
}

export type GoalArray = Goal[];

export type GoalArrayOrNull = Nullable<Goal[]>;

export type ProofView = Nullable<ProofViewType>;