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

export enum QueryType {
    search = "search", 
    about = "about", 
    check = "check",
    locate = "locate", 
    print = "print"
}
export interface QueryResultBase {
    statement: Nullable<PpString>;
}
export interface SearchResult extends QueryResultBase {
    name: PpString;
}
export interface CollapsibleSearchResult extends SearchResult {
    collapsed: boolean;
}
export interface SearchResultType {
    type: QueryType.search;
    data : CollapsibleSearchResult[]
};
export interface SearchNotification extends SearchResult {
    id: string; 
};
export interface QueryNotification extends QueryResultBase {
    id: string;
}
export interface CheckResultType extends QueryResultBase {
    type: QueryType.check;
}
export interface AboutResultType extends QueryResultBase {
    type: QueryType.about;
}
export interface LocateResultType extends QueryResultBase {
    type: QueryType.locate;
}
export interface PrintResultType extends QueryResultBase {
    type: QueryType.print;
}
export interface QueryError {
    code: integer; 
    message: string;
}
export type QueryResultType = 
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
    result: QueryResultType,
    error?: QueryError,
    expanded?: boolean
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
