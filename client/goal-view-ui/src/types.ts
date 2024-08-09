import { integer } from "vscode-languageclient";
import { PpString } from "pp-display";
type Nullable<T> = T | null;

export interface Goal {
    id: string,
    goal: PpString, 
    hypotheses: PpString[],
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