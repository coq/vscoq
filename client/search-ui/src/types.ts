export interface SearchNotification {
    id: string; 
    name: string; 
    statement: string;
};
export interface AboutNotification {
    id: string; 
    statement: string; 
};
export interface CheckNotification {
    id: string; 
    statement: string; 
};

export enum QueryType {
    search = "search", 
    about = "about", 
    check = "check"
}

export interface SearchResultType {
    type: "search";

    data : {
        name: string; 
        statement: string;
    }[]
};
export interface CheckResultType {
    type: "check";
    statement: string;
}
export interface AboutResultType {
    type: "about"; 
    statement: string; 
}

export type QueryResult = SearchResultType | CheckResultType | AboutResultType;

export interface Query {
    pattern: string; 
    type: QueryType; 
};

export interface QueryTab {
    id: string, 
    pattern: string, 
    type: QueryType, 
    result: QueryResult,
};

export type QueryPanelState = {
    currentTab: number;
    tabs: QueryTab[];
};

export type VsCodeState = {
    state?: QueryPanelState,
    history?: string[],
    historyIndex?: number, 
};
