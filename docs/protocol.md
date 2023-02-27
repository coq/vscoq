git s# LSP

vscoq uses the [language server protocol](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/). 

We implement a few custom verbs that we detail here. 

## Configuration 

We wend the configuration items needed by the server by using `vscoq/configuration`

```typescript
interface Configuration {
    //Delegation mode 
    delegate: string
    //Number of workers if relevant
    workers: int
    //Proof checking mode
    coqMode: string
}
```

## Highlights

For providing highlights which reflect the current internal state of coq, we provide "vscoq/updateHighlights" which returns an object containing 

``` typescript
interface Highlights {
    //Document idefinfier
    uri: VersionedTextDocumentIdentifier;
    // The ranges of lines of code that were parsed by the server
    parsedRange: vscode.Range[];
    // The ranges of lines of code currently being processed by the server
    processingRange: vscode.Range[];
    // The ranges of lines of code that have been processed by the server
    processedRange: vscode.Range[];
}
```

The parsed, processing and processed range correspond to the ranges of lines in the document that have the coresponding type. 
By default, we display the processed lines in the VSCode gutter.

## Goal view 

For the goal view we provide a request verb `vscoq/updateProofView` and its corresponding response. 

```typescript 

//The hypothesis type from coq
interface Hypothesis {
    identifiers: string[];
    type: string;
}

//A coq goal and its corresponding hypotheses
interface Goal {
    id: integer;
    goal: string;
    hypotheses: Hypothesis[];
}

//The update proof view request requires a URI and a Position in the document
interface UpdateProofViewRequest {
    textDocument: VersionedTextDocumentIdentifier;
    position: vscode.Position;
}

// the reponse to your request returns the goals, the shelvedGoals and the given up goals
interface UpdateProofViewResponse {
    goals: Goal[];
    shelvedGoals: Goal[];
    givenUpGoals: Goal[];
}

```

## Query panel

For the query panel we provide a request verb `vscoq/search` and its corresponding response `vscoq/searchResult`. 

``` typescript

interface SearchCoqRequest {
    // This should be a uuid provided by the client
    id: string;
    // a document uri as given through the vscode api
    textDocument: VersionedTextDocumentIdentifier;
    // The pattern to use for the coq search command
    pattern: string; 
    // The position the cursor is in the document (this is to infer the current coq state)
    position: Position;
}

interface SearchCoqHandshake {
    //Returns the provided uuid
    id: string;
    //If the search was succesful just returns ok
    result?: boolean;
    //Returns any relevant error message
    error?: any;

}

interface SearchCoqResult {
    //The uuid of the search associated to this result
    id: string;
    // The name of the relevant search result (theorem or lemma or etc... in coq)
    name: string; 
    // The statement of the relevant search result
    statement: string;
}
```

By default the coq Search command as asynchronous. Therefore, the language server first sends a handshake either with an OK code, or with an error. It then sends each result one by one through the SearchCoqResult interface. The id corresponds to a uuid given to each search request. 

We also provide the requests for the "check" and "about" queries, with plans to support more in the future. 
Note that the "check" and about "about" queries are synchronous and do not require a seperate verb for their responses. 
Verbs: `vscoq/check`, `vscoq/about`.

```typescript

export interface AboutCoqRequest {
    textDocument: VersionedTextDocumentIdentifier;
    pattern: string; 
    position: Position;
    goalIndex?: number;
}

export type AboutCoqResponse = string;

export interface CheckCoqRequest {
    textDocument: VersionedTextDocumentIdentifier;
    pattern: string; 
    position: Position;
    goalIndex?: number;
};

export type CheckCoqResponse = string; 
```

