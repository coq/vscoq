import { integer } from "vscode-languageclient";

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
export interface LocateNotification {
    id: string; 
    statement: string; 
};
export interface PrintNotification {
    id: string; 
    statement: string; 
};


export enum QueryType {
    search = "search", 
    about = "about", 
    check = "check",
    locate = "locate", 
    print = "print"
}

export interface SearchResultType {
    type: QueryType.search;

    data : {
        name: string; 
        statement: string;
        collapsed: boolean;
    }[]
};
export interface CheckResultType {
    type: QueryType.check;
    statement: string;
}
export interface AboutResultType {
    type: QueryType.about;
    statement: string; 
}
export interface LocateResultType {
    type: QueryType.locate;
    statement: string;
}
export interface PrintResultType {
    type: QueryType.print;
    statement: string;
}
export interface QueryError {
    code: integer; 
    message: string;
}

export type QueryResult = 
    SearchResultType
    | CheckResultType
    | AboutResultType
    | LocateResultType
    | PrintResultType;

export interface Query {
    pattern: string; 
    type: QueryType; 
};


export interface QueryTab {
    id: string, 
    title: string, 
    pattern: string, 
    type: QueryType, 
    result: QueryResult,
    error?: QueryError
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
