/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */
'use strict';

import {RequestType} from 'vscode-jsonrpc';
import {
	createConnection, IConnection, TextDocumentSyncKind,
	TextDocuments, ITextDocument, Diagnostic, DiagnosticSeverity,
	InitializeParams, InitializeResult, TextDocumentIdentifier, TextDocumentPosition,
  DidChangeTextDocumentParams,
	CompletionItem, CompletionItemKind, PublishDiagnosticsParams, ServerCapabilities
} from 'vscode-languageserver';
import * as vscodeLangServer from 'vscode-languageserver';
import * as util from 'util';
 
import {CoqDocument} from './document';
import * as coqproto from './protocol';
import {CoqTopSettings, Settings} from './protocol';


let currentSettings : CoqTopSettings;

// Create a connection for the server. The connection uses 
// stdin / stdout for message passing
let connection: IConnection = createConnection(process.stdin, process.stdout);

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

let coqInstances : { [uri: string] : CoqDocument } = {};


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
	currentSettings = settings.coqtop;
	connection.console.log('Changed path to: ' + currentSettings.coqPath);
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
connection.onCompletion((textDocumentPosition: TextDocumentPosition): CompletionItem[] => {
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

connection.onRequest(coqproto.InterruptCoqRequest.type, (params: coqproto.CoqTopParams) => {
  var doc = coqInstances[params.uri];
  if(doc)
    doc.coq.interrupt();
  else
    return null;
});
connection.onRequest(coqproto.QuitCoqRequest.type, (params: coqproto.CoqTopParams) => {
  var doc = coqInstances[params.uri];
  if(doc)
    doc.coq.quit();
  else
    return null;
});
connection.onRequest(coqproto.ResetCoqRequest.type, (params: coqproto.CoqTopParams) => {
  var doc = coqInstances[params.uri];
  if(doc)
    doc.coq.reset();
  else
    return null;
});
connection.onRequest(coqproto.StepForwardRequest.type, (params: coqproto.CoqTopParams) => {
  var doc = coqInstances[params.uri];
  if(doc)
    return doc.coq.stepForward();
  else
    return null;
});
connection.onRequest(coqproto.StepBackwardRequest.type, (params: coqproto.CoqTopParams) => {
  var doc = coqInstances[params.uri];
  if(doc)
    return doc.coq.stepBackward();
  else
    return null;
});
connection.onRequest(coqproto.InterpretToPointRequest.type, (params: coqproto.CoqTopInterpretToPointParams) => {
  var doc = coqInstances[params.uri];
  if(doc)
    return doc.coq.interpretToPoint(params.offset);
  else
    return null;
});
connection.onRequest(coqproto.InterpretToEndRequest.type, (params: coqproto.CoqTopParams) => {
  var doc = coqInstances[params.uri];
  if(doc)
    return doc.coq.interpretToEnd();
  else
    return null;
});
connection.onRequest(coqproto.GoalRequest.type, (params: coqproto.CoqTopParams) => {
  var doc = coqInstances[params.uri];
  if(doc)
    return doc.coq.getGoals();
  else
    return null;
});
connection.onRequest(coqproto.QueryRequest.type, (params: coqproto.CoqTopQueryParams) => {
  var doc = coqInstances[params.uri];
  if(doc)
    switch(params.queryFunction) {
    case coqproto.QueryFunction.Locate:
      return doc.coq.locate(params.query);
    case coqproto.QueryFunction.Check:
      return doc.coq.check(params.query);
    case coqproto.QueryFunction.Search:
      return doc.coq.search(params.query);
    case coqproto.QueryFunction.SearchAbout:
      return doc.coq.searchAbout(params.query);
    default:
      return null;
    }
  else
    return null;
});
connection.onRequest(coqproto.ResizeWindowRequest.type, (params: coqproto.CoqTopResizeWindowParams) => {
  var doc = coqInstances[params.uri];
  if(doc)
    return doc.coq.resizeWindow(params.columns);
  else
    return;
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


connection.onDidOpenTextDocument((params) => {
  var uri = params.uri;
  coqInstances[uri] = new CoqDocument(currentSettings, uri, params.text, connection.console, {
    sendHighlightUpdates: (h) => sendHighlightUpdates(uri, h),
    sendDiagnostics: (diagnostics) => sendDiagnostics(uri, diagnostics),
    sendMessage: (level, message: string) =>
      connection.sendNotification(coqproto.CoqMessageNotification.type, {
        level: level,
        message: message,
        uri: uri,
      }),
    sendReset: () =>
      connection.sendNotification(coqproto.CoqResetNotification.type, {uri: uri}),
    sendStateViewUrl: (stateUrl: string) =>
      connection.sendNotification(coqproto.CoqStateViewUrlNotification.type, {uri: uri, stateUrl: stateUrl}),
  });
});

connection.onDidChangeTextDocument((params) => {
  const doc = coqInstances[params.uri];

  if(doc) {
    doc.textEdit(params.contentChanges);
  }
});

connection.onDidCloseTextDocument((params) => {
	// A text document got closed in VSCode.
	// params.uri uniquely identifies the document.
  const doc = coqInstances[params.uri];
  doc.close();
  delete coqInstances[params.uri];
});


// Listen on the connection
connection.listen();