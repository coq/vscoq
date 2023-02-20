type Nullable<T> = T | null;

export type Goal = {
    id: string,
    goal: string, 
    hypotheses: {
        identifiers: string[],
        type: string
    }[],
    isOpen: boolean, 
    displayId: number
};

export type GoalArray = Goal[];

export type GoalArrayOrNull = Nullable<Goal[]>;