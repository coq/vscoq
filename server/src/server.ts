'use strict';
import {rangeToString} from './util/text-util';

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
import {CoqTopSettings, CoqSettings, Settings} from './protocol';
import {CoqProject} from './CoqProject';

// Create a connection for the server. The connection uses 
// stdin / stdout for message passing
export let connection: IConnection = createConnection();

export let project : CoqProject = null;

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
  console.log = (e) => {connection.console.log(">>> " + e)};
  console.info = (e) => {connection.console.info(">>> " + e)};
  console.warn = (e) => {connection.console.warn(">>> " + e)};
  console.error = (e) => {connection.console.error(">>> " + e)};

  connection.console.log(`Coq Language Server: process.version: ${process.version}, process.arch: ${process.arch}}`);
  // connection.console.log(`execArgv: ${process.execArgv.join(' ')}`);
  // connection.console.log(`argv: ${process.argv.join(' ')}`);
  // connection.console.log('coq path: ' + currentSettings.coqPath);
	workspaceRoot = params.rootPath;

  // let x: vscodeLangServer.RemoteConsole = {
  //   log: (x) => {},
  //   error: (x) => {},
  //   warn: (x) => {},
  //   info: (x) => {}
  // }
  // project = new CoqProject(params.rootPath, x);
  project = new CoqProject(params.rootPath, connection);

  // var x : ServerCapabilities;
	return {
		capabilities: <ServerCapabilities>{
			textDocumentSync: TextDocumentSyncKind.Incremental,
			// Tell the client that the server support code complete
			completionProvider: {
				resolveProvider: true
			},
      documentLinkProvider: {
        resolveProvider: true
      },
      documentSymbolProvider: true,
      definitionProvider: true,
		}
	}
});

connection.onShutdown(() => {
  project.shutdown();
})

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
	let settings = change.settings as Settings;
	project.updateSettings(settings);
	connection.console.log('Changed path to: ' + project.settings.coqtop.binPath);
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
	return [];
	// 	{
	// 		label: 'idtac',
	// 		kind: CompletionItemKind.Snippet,
	// 		data: 1
	// 	},
	// 	{
	// 		label: 'Definition',
	// 		kind: CompletionItemKind.Keyword,
	// 		data: 2
	// 	},
	// 	{
	// 		label: 'reflexivity.',
	// 		kind: CompletionItemKind.Text,
	// 		data: 4
	// 	}
	// ]
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

connection.onRequest(coqproto.InterruptCoqRequest.type, (params: coqproto.CoqTopParams, token: CancellationToken) => {
  return project.lookup(params.uri)
    .interrupt();
});
connection.onRequest(coqproto.QuitCoqRequest.type, (params: coqproto.CoqTopParams, token: CancellationToken) : Thenable<void> => {
  return project.lookup(params.uri)
    .quitCoq();
});
connection.onRequest(coqproto.ResetCoqRequest.type, (params: coqproto.CoqTopParams, token: CancellationToken) => {
  return project.lookup(params.uri)
    .resetCoq();
});
connection.onRequest(coqproto.StepForwardRequest.type, (params: coqproto.CoqTopParams, token: CancellationToken) => {
  return project.lookup(params.uri)
    .stepForward(token);
});
connection.onRequest(coqproto.StepBackwardRequest.type, (params: coqproto.CoqTopParams, token: CancellationToken) => {
  return project.lookup(params.uri)
    .stepBackward(token);
});
connection.onRequest(coqproto.InterpretToPointRequest.type, (params: coqproto.CoqTopInterpretToPointParams, token: CancellationToken) => {
  return project.lookup(params.uri)
    .interpretToPoint(params.location, params.synchronous, token);
});
connection.onRequest(coqproto.InterpretToEndRequest.type, (params: coqproto.InterpretToEndParams, token: CancellationToken) => {
  return project.lookup(params.uri)
    .interpretToEnd(params.synchronous, token);
});
connection.onRequest(coqproto.GoalRequest.type, (params: coqproto.CoqTopParams, token: CancellationToken) => {
  return project.lookup(params.uri)
    .getGoal();
});
connection.onRequest(coqproto.CachedGoalRequest.type, (params: coqproto.CachedGoalParams, token: CancellationToken) => {
  return project.lookup(params.uri)
    .getCachedGoal(params.position, params.direction);
});
connection.onRequest(coqproto.QueryRequest.type, async (params: coqproto.CoqTopQueryParams, token: CancellationToken) => {
  return { searchResults: await project.lookup(params.uri).query(params.queryFunction, params.query) || "" };
});
connection.onRequest(coqproto.ResizeWindowRequest.type, (params: coqproto.CoqTopResizeWindowParams, token: CancellationToken) => {
  return project.lookup(params.uri)
    .setWrappingWidth(params.columns);
});

connection.onRequest(coqproto.LtacProfResultsRequest.type, (params: coqproto.CoqTopLtacProfResultsParams, token: CancellationToken) => {
  return project.lookup(params.uri)
    .requestLtacProfResults(params.offset);
});

connection.onRequest(coqproto.SetDisplayOptionsRequest.type, (params: coqproto.CoqTopSetDisplayOptionsParams, token: CancellationToken) => {
  return project.lookup(params.uri)
    .setDisplayOptions(params.options);
});

connection.onRequest(coqproto.FinishComputationsRequest.type, (params: coqproto.CoqTopSetDisplayOptionsParams, token: CancellationToken) => {
  return project.lookup(params.uri)
    .finishComputations();
});

connection.onRequest(coqproto.GetSentencePrefixTextRequest.type, (params: coqproto.DocumentPositionParams, token: CancellationToken) => {
  return project.lookup(params.uri)
    .getSentencePrefixTextAt(params.position);
});


function sendHighlightUpdates(documentUri: string, highlights: coqproto.Highlights) {
  connection.sendNotification(coqproto.UpdateHighlightsNotification.type,
    Object.assign(highlights, {uri: documentUri}));
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

export interface DocumentLinkParams {
    /**
     * The document to provide document links for.
     */
    textDocument: TextDocumentIdentifier;
}

connection.onDefinition((params: vscodeLangServer.TextDocumentPositionParams) : Promise<vscodeLangServer.Location|vscodeLangServer.Location[]>|vscodeLangServer.Location|vscodeLangServer.Location[] => {
  const doc = project.lookup(params.textDocument.uri);
  if(!doc)
    return [];
  else
    return doc.provideDefinition(params.position);
})

connection.onDocumentSymbol((params:vscodeLangServer.DocumentSymbolParams) : vscodeLangServer.SymbolInformation[] => {
  const doc = project.lookup(params.textDocument.uri);
  if(!doc)
    return [];
  else
    return doc.provideSymbols();
})

connection.onDocumentLinks((p:DocumentLinkParams,token: CancellationToken) : Promise<vscodeLangServer.DocumentLink[]> => {
  return Promise.resolve([]);
  // return project.lookup(p.textDocument.uri)
    // .provideDocumentLinks(token);
})

connection.onDocumentLinkResolve((link: vscodeLangServer.DocumentLink,token: CancellationToken) : vscodeLangServer.DocumentLink => {
return link;
  // connection.console.log("onDocumentLinkResolve: " + link);
  // return link;  
})

connection.onDidOpenTextDocument((params: vscodeLangServer.DidOpenTextDocumentParams) => {
  const uri = params.textDocument.uri; 
  project.open(params.textDocument, {
    sendHighlightUpdates: (h) => sendHighlightUpdates(uri, h),
    sendDiagnostics: (diagnostics) => sendDiagnostics(uri, diagnostics),
    sendMessage: (level, message: string, rich_message?: any) =>
      connection.sendNotification(coqproto.CoqMessageNotification.type, <coqproto.NotifyMessageParams>{
        level: level,
        message: message,
        uri: uri,
        rich_message: rich_message,
      }),
    sendReset: () =>
      connection.sendNotification(coqproto.CoqResetNotification.type, {uri: uri}),
    sendStmFocus: (focus: Position) =>
      connection.sendNotification(coqproto.CoqStmFocusNotification.type, {uri: uri, position: focus}),
    sendLtacProfResults: (results: coqproto.LtacProfResults) =>
      connection.sendNotification(coqproto.CoqLtacProfResultsNotification.type, {uri: uri, results: results}),
    sendCoqtopStart: () =>
      connection.sendNotification(coqproto.CoqtopStartNotification.type, {uri: uri}),
    sendCoqtopStop: (reason: coqproto.CoqtopStopReason, message?: string) =>
      connection.sendNotification(coqproto.CoqtopStopNotification.type, {uri: uri, reason: reason, message: message}),
  });

});

connection.onDidChangeTextDocument((params) => {
  try {
    return project.lookup(params.textDocument.uri)
      .applyTextEdits(params.contentChanges, params.textDocument.version);
  } catch(err) {
    connection.console.error(err.toString());
  }
});

connection.onDidCloseTextDocument((params) => {
	// A text document got closed in VSCode.
	// params.uri uniquely identifies the document.
  project.close(params.textDocument.uri);
});


// Listen on the connection
connection.listen();