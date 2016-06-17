/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */
'use strict';

import {RequestType, CancellationToken} from 'vscode-jsonrpc';
import {
	createConnection, IConnection, TextDocumentSyncKind,
	TextDocuments, TextDocument, Diagnostic, DiagnosticSeverity,
	InitializeParams, InitializeResult, TextDocumentIdentifier, Position, TextDocumentPositionParams,
  DidChangeTextDocumentParams,
  CodeLensParams, RequestHandler,
	CompletionItem, CompletionItemKind, PublishDiagnosticsParams, ServerCapabilities, CodeActionParams, Command, CodeLens, Hover
} from 'vscode-languageserver';
import * as vscodeLangServer from 'vscode-languageserver';
import * as util from 'util';
 
import {CoqDocument} from './document';
import * as coqproto from './protocol';
import {CoqTopSettings, Settings} from './protocol';
import {CoqProject} from './CoqProject';



// Create a connection for the server. The connection uses 
// stdin / stdout for message passing
let connection: IConnection = createConnection(process.stdin, process.stdout);


let project : CoqProject = null;

// // Create a simple text document manager. The text document manager
// // supports full document sync only
// let documents: TextDocuments = new TextDocuments();
// // Make the text document manager listen on the connection
// // for open, change and close text document events
// documents.listen(connection);

// After the server has started the client sends an initilize request. The server receives
// in the passed params the rootPath of the workspace plus the client capabilites. 
let workspaceRoot: string;
connection.onInitialize((params): InitializeResult => {
  connection.console.log(`Coq Language Server: process.version: ${process.version}, process.arch: ${process.arch}}`);
  // connection.console.log('coq path: ' + currentSettings.coqPath);
	workspaceRoot = params.rootPath;
  
  project = new CoqProject(params.rootPath, connection.console);
  
  // var x : ServerCapabilities;
	return {
		capabilities: {
			textDocumentSync: TextDocumentSyncKind.Incremental,
			// Tell the client that the server support code complete
			completionProvider: {
				resolveProvider: true
			}
		}
	}
});



// documents.onDidChangeContent((change) => {
//   var uri = change.document.uri;
// });
// The content of a text document has changed. This event is emitted
// when the text document first opened or when its content has changed.
// documents.onDidChangeContent((change) => {
//   var uri = change.document.uri;
//   if (typeof coqInstances[uri] === "undefined") {
//   	connection.console.log(`${uri} opened.`);
//     coqInstances[uri] = new CoqDocument(coqPath, change.document, connection.console, {
//       sendHighlightUpdates: (h) => sendHighlightUpdates(uri, h),
//       sendDiagnostics: (diagnostics) => sendDiagnostics(uri, diagnostics)
//       });
//   }
//   else {
//   }
// });


// The settings have changed. Is send on server activation
// as well.
connection.onDidChangeConfiguration((change) => {
	let settings = <Settings>change.settings;
	project.updateSettings(settings);
	connection.console.log('Changed path to: ' + project.settings.coqtop.coqPath);
	// Revalidate any open text documents
	//documents.all().forEach(validateTextDocument);
});


// connection.onDidChangeWatchedFiles((change) => {
// 	// Monitored files have change in VSCode
// 	connection.console.log('We received a file change event');
// });

process.on('SIGBREAK', function () {
  connection.console.log('SIGBREAK fired')
});


// This handler provides the initial list of the completion items.
connection.onCompletion((textDocumentPosition: TextDocumentPositionParams): CompletionItem[] => {
	// The pass parameter contains the position of the text document in 
	// which code complete got requested. For the example we ignore this
	// info and always provide the same completion items.
	return [
		{
			label: 'idtac',
			kind: CompletionItemKind.Snippet,
			data: 1
		},
		{
			label: 'Definition',
			kind: CompletionItemKind.Keyword,
			data: 2
		},
		{
			label: 'reflexivity.',
			kind: CompletionItemKind.Text,
			data: 4
		}
	]
});


// This handler resolve additional information for the item selected in
// the completion list.
connection.onCompletionResolve((item: CompletionItem): CompletionItem => {
	if (item.data === 1) {
		item.detail = 'Tactic'
	} else if (item.data === 4) {
		item.detail = 'JavaScript details',
		item.documentation = 'solves by reflexivity'
	}
	return item;
});

// export interface RequestHandler<P, R, E> {
//     (params: P, token: CancellationToken): R | ResponseError<E> | Thenable<R | ResponseError<E>>;
// }

connection.onRequest<coqproto.CoqTopParams, void, void>(coqproto.InterruptCoqRequest.type, (params: coqproto.CoqTopParams, token: CancellationToken) => {
  return project.lookup(params.uri)
    .coq.interrupt();
});
connection.onRequest<coqproto.CoqTopParams, void, void>(coqproto.QuitCoqRequest.type, (params: coqproto.CoqTopParams) : Thenable<void> => {
  return project.lookup(params.uri)
    .coq.quit();
});
connection.onRequest<coqproto.CoqTopParams, void, void>(coqproto.ResetCoqRequest.type, (params: coqproto.CoqTopParams) => {
  return project.lookup(params.uri)
    .coq.reset();
});
connection.onRequest<coqproto.CoqTopParams, coqproto.CoqTopGoalResult, void>(coqproto.StepForwardRequest.type, (params: coqproto.CoqTopParams) => {
  return project.lookup(params.uri)
    .coq.stepForward();
});
connection.onRequest<coqproto.CoqTopParams, coqproto.CoqTopGoalResult, void>(coqproto.StepBackwardRequest.type, (params: coqproto.CoqTopParams) => {
  return project.lookup(params.uri)
    .coq.stepBackward();
});
connection.onRequest<coqproto.CoqTopParams, coqproto.CoqTopGoalResult, void>(coqproto.InterpretToPointRequest.type, (params: coqproto.CoqTopInterpretToPointParams) => {
  return project.lookup(params.uri)
    .coq.interpretToPoint(params.offset);
});
connection.onRequest<coqproto.CoqTopParams, coqproto.CoqTopGoalResult, void>(coqproto.InterpretToEndRequest.type, (params: coqproto.CoqTopParams) => {
  return project.lookup(params.uri)
    .coq.interpretToEnd();
});
connection.onRequest<coqproto.CoqTopParams, coqproto.CoqTopGoalResult, void>(coqproto.GoalRequest.type, (params: coqproto.CoqTopParams) => {
  return project.lookup(params.uri)
    .coq.getGoals();
});
connection.onRequest<coqproto.CoqTopParams, coqproto.CoqTopGoalResult, void>(coqproto.QueryRequest.type, (params: coqproto.CoqTopQueryParams) => {
  switch(params.queryFunction) {
  case coqproto.QueryFunction.Locate:
    return project.lookup(params.uri).coq.locate(params.query);
  case coqproto.QueryFunction.Check:
    return project.lookup(params.uri).coq.check(params.query);
  case coqproto.QueryFunction.Search:
    return project.lookup(params.uri).coq.search(params.query);
  case coqproto.QueryFunction.SearchAbout:
    return project.lookup(params.uri).coq.searchAbout(params.query);
  default:
    return null;
  }
});
connection.onRequest<coqproto.CoqTopParams, void, void>(coqproto.ResizeWindowRequest.type, (params: coqproto.CoqTopResizeWindowParams) => {
  return project.lookup(params.uri)
    .coq.resizeWindow(params.columns);
});

connection.onRequest<coqproto.CoqTopParams, void, void>(coqproto.LtacProfSetRequest.type, (params: coqproto.CoqTopLtacProfSetParams) => {
  return project.lookup(params.uri)
    .coq.ltacProfSet(params.enabled);
});
connection.onRequest<coqproto.CoqTopLtacProfResultsParams, coqproto.CoqTopGoalResult, void>(coqproto.LtacProfResultsRequest.type, (params: coqproto.CoqTopLtacProfResultsParams) => {
  return project.lookup(params.uri)
    .coq.ltacProfResults(params.offset);
});


function sendHighlightUpdates(documentUri: string, highlights: coqproto.Highlight[]) {
  connection.sendNotification(coqproto.UpdateHighlightsNotification.type, {
    highlights: highlights, uri: documentUri});
}

function sendDiagnostics(documentUri: string, diagnostics: Diagnostic[]) {
  connection.sendDiagnostics({
    diagnostics: diagnostics,
    uri: documentUri, 
  });
}

connection.onCodeAction((params:CodeActionParams) => {
  return <Command[]>[];
});

connection.onCodeLens((params:CodeLensParams) => {
  return [];
});

connection.onCodeLensResolve((params:CodeLens) => {
  return params;
});


connection.onDidOpenTextDocument((params) => {
  const uri = params.textDocument.uri;
  project.open(uri, params.textDocument.text, {
    sendHighlightUpdates: (h) => sendHighlightUpdates(uri, h),
    sendDiagnostics: (diagnostics) => sendDiagnostics(uri, diagnostics),
    sendMessage: (level, message: string, rich_message?: any) =>
      connection.sendNotification(coqproto.CoqMessageNotification.type, {
        level: level,
        message: message,
        uri: uri,
        rich_message: rich_message,
      }),
    sendReset: () =>
      connection.sendNotification(coqproto.CoqResetNotification.type, {uri: uri}),
    sendStateViewUrl: (stateUrl: string) =>
      connection.sendNotification(coqproto.CoqStateViewUrlNotification.type, {uri: uri, stateUrl: stateUrl}),
    sendComputingStatus : (status: coqproto.ComputingStatus, computeTimeMS: number) =>
      connection.sendNotification(coqproto.CoqComputingStatusNotification.type, {uri: uri, status: status, computeTimeMS: computeTimeMS}),      
  });

});

connection.onDidChangeTextDocument((params) => {
  return project.lookup(params.textDocument.uri)
    .textEdit(params.contentChanges);
});

connection.onDidCloseTextDocument((params) => {
	// A text document got closed in VSCode.
	// params.uri uniquely identifies the document.
  project.close(params.textDocument.uri);
});


// Listen on the connection
connection.listen();