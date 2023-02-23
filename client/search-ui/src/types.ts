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

export interface SearchResultType {
    name: string; 
    statement: string;
};
export type CheckResultType = string; 
export type AboutResultType = string; 

export type QueryResult = SearchResultType[] | CheckResultType | AboutResultType | null;

export enum QueryType {
    search = "Search", 
    about = "About", 
    check = "Check"
}

export interface Query {
    pattern: string; 
    type: QueryType; 
};

export interface QueryTab {
    id: string, 
    pattern: string, 
    type: QueryType, 
    results: QueryResult,
};
