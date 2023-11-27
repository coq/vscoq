# LSP

vscoq uses the [language server protocol](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/). 

We implement a few custom verbs that we detail here. 

## Configuration 

We handle the `workspace/configuration` and `workspace/didChangeConfiguration` notifications. 
The settings that get sent to the server are as follows: 

### Settings for checking proofs

```typescript

enum DelegationMode {
    none: "None", 
    skip: "Skip",
    delegate: "Delegate"
}

enum Mode {
    Manual: 0, 
    Continuous
}

interface Proof {
    //Delegation mode 
    delegate: DelegationMode
    //Number of workers if relevant
    workers: int
    //Proof checking mode 
    mode: Mode
}
```

### Settings for the goal view

```typescript
// Should we send errors and diagnostics to the message 
// panel of the goal view ?
interface Messages {
    full: bool;
}

//diff mode
enum DiffMode {
    On: "on", 
    Off: "off",
    Removed: "removed" 
}

interface Diff {
    mode: DiffMode
}

//Config settings pertaining to the goal view
interface Goals {
    diff: Diff
    messages: Messages
}
```

### Settings for completion (experimental)
```typescript
enum RankingAlgorithm {
    SplitTypeIntersection = 0, 
    StructuredSplitUnification
}

interface Completion {
    enable: bool
    algorithm: RankingAlgorithm
    unificationLimit: float
    sizeFactor: float
}
```

### Settings for diagnostics 

```typescript
interface Diagnostics {
    enable: bool
    full: bool
}
```

### Configuration message

```typescript
interface Configuration {
    proof: Proof
    goals: Goals
    completion: Completion
    diagnostics: Diagnostics
}
```

## Highlights

For providing highlights which reflect the current internal state of coq, we provide "vscoq/updateHighlights" which returns an object containing 

``` typescript
interface UpdateHighlightsNotification {
    //Document idefinfier
    uri: Uri;
    // The ranges of lines of code currently being processed by the server
    processingRange: vscode.Range[];
    // The ranges of lines of code that have been processed by the server
    processedRange: vscode.Range[];
}
```

The processing and processed range correspond to the ranges of lines in the document that have the coresponding type. 
By default, we display the processed lines in the VSCode gutter.

## Goal view 

For the goal view we provide a request verb `vscoq/updateProofView` and its corresponding response. 

We now make use of PpStrings to display the goals with syntaxic coloration.

We also have a move cursor notification to inform the client to move the cursor (used in manual mode).

```typescript 
type PpTag = string;

type BlockType =
  | ["Pp_hbox"]
  | ["Pp_vbox", integer]
  | ["Pp_hvbox", integer]
  | ["Pp_hovbox", integer];

type PpString =
  | ["Ppcmd_empty"]
  | ["Ppcmd_string", string]
  | ["Ppcmd_glue", PpString[]]
  | ["Ppcmd_box", BlockType, PpString]
  | ["Ppcmd_tag", PpTag, PpString]
  | ["Ppcmd_print_break", integer, integer]
  | ["Ppcmd_force_newline"]
  | ["Ppcmd_comment", string[]];

//A coq goal and its corresponding hypotheses
interface Goal {
    id: integer;
    goal: PpString;
    hypotheses: PpString[];
}

//We also display shelved and given up goals
interface ProofViewGoals {
    goals: Goal[];
    shelvedGoals: Goal[];
    givenUpGoals: Goal[];
}

//We display messages in the goal panel
enum MessageSeverity {
    error = "Error",
    warning = "Warning", 
    info = "Information"
}
type CoqMessage = [MessageSeverity, PpString];


// The proof view notification is sent from the server to the client
interface ProofViewNotification {
    proof: Nullable<ProofViewGoals>;
    messages: CoqMessage[];
}

// Sent from the server to the client after a stepForward or stepBack
interface MoveCursorNotification {
    uri: Uri; 
    range: Range; 
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
}

interface SearchCoqResult {
    //The uuid of the search associated to this result
    id: string;
    // The name of the relevant search result (theorem or lemma or etc... in coq)
    name: PpString; 
    // The statement of the relevant search result
    statement: PpString;
}
```

By default the coq Search command as asynchronous. Therefore, the language server first sends a handshake either with an OK code, or with an error. It then sends each result one by one through the SearchCoqResult notification. The id corresponds to a uuid given to each search request. 

We also provide the requests for the `vscoq/check`, `vscoq/about`, `vscoq/locate` and `vscoq/print` queries, with plans to support more in the future. 
These queries are synchronous and do not require a seperate verb for their responses. 

```typescript

interface AboutCoqRequest {
    textDocument: VersionedTextDocumentIdentifier;
    pattern: string; 
    position: Position;
}

type AboutCoqResponse = PpString;

interface CheckCoqRequest {
    textDocument: VersionedTextDocumentIdentifier;
    pattern: string; 
    position: Position;
};

type CheckCoqResponse = PpString; 

interface LocateCoqRequest {
    textDocument: VersionedTextDocumentIdentifier;
    pattern: string; 
    position: Position;
};

type LocateCoqResponse = PpString; 

interface PrintCoqRequest {
    textDocument: VersionedTextDocumentIdentifier;
    pattern: string; 
    position: Position;
};

type PrintCoqResponse = PpString; 
```

