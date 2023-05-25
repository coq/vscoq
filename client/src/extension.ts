import {workspace, window, commands, ExtensionContext,
  TextEditorSelectionChangeEvent,
  TextEditorSelectionChangeKind,
  TextEditor,
  ViewColumn, 
} from 'vscode';

import {
  LanguageClientOptions,
  ServerOptions, VersionedTextDocumentIdentifier
} from 'vscode-languageclient/node';

import Client from './client';
import { updateServerOnConfigurationChange } from './configuration';
import { checkVersion } from './utilities/versioning';
import {initializeDecorations} from './Decorations';
import GoalPanel from './panels/GoalPanel';
import SearchViewProvider from './panels/SearchViewProvider';
import { SearchCoqResult, UpdateProofViewRequest } from './protocol/types';
import { 
    sendInterpretToPoint,
    sendInterpretToEnd,
    sendStepForward,
    sendStepBackward
} from './manualChecking';
import { makeCursorPositionUpdateProofViewRequestParams, makeExecutionUpdateProofViewRequestParams } from './utilities/requests';
import { DocumentStateViewProvider } from './panels/DocumentStateViewProvider';


let client: Client;

export function activate(context: ExtensionContext) {

    function registerVscoqTextCommand(command: string, callback: (textEditor: TextEditor, ...args: any[]) => void) {
        context.subscriptions.push(commands.registerTextEditorCommand('vscoq.' + command, callback));
    };
    
	const config = workspace.getConfiguration('vscoq');

	let serverOptions: ServerOptions = {
		/*
		command: "perf",
		args: ["record","--call-graph=dwarf", "--", config.path].concat(config.args)
		*/
		command: config.path,
		args: config.args
	};

	let clientOptions: LanguageClientOptions = {
		documentSelector: [{ scheme: 'file', language: 'coq' }],
        initializationOptions: config
	};

	// Create the language client and start the client.
	client = new Client(
		serverOptions,
		clientOptions
	);

    //register the search view provider 
    const searchProvider = new SearchViewProvider(context.extensionUri, client);
    context.subscriptions.push(window.registerWebviewViewProvider(SearchViewProvider.viewType, searchProvider));

    const documentStateProvider = new DocumentStateViewProvider(client); 
    context.subscriptions.push(workspace.registerTextDocumentContentProvider("vscoq-document-state", documentStateProvider));

    const launchQuery = (editor: TextEditor, type: string)=> {
        const selection = editor.selection;
        const {end, start} = selection; 
        if(end.line !== start.line) {return;} //don't allow for multiline selections
        //either use the user selection or if no selection than infer the word under the cursor
        const wordAtCurorRange = (end.character !== start.character) ? selection : editor.document.getWordRangeAtPosition(end);
        if(!wordAtCurorRange) {return; } //there is no word: do nothing
        const queryText = editor.document.getText(wordAtCurorRange);
        //focus on the query panel
        commands.executeCommand('vscoq.search.focus');
        //launch the query
        searchProvider.launchQuery(queryText, type);
    };


    registerVscoqTextCommand('searchCursor', (editor) => launchQuery(editor, "search"));
    registerVscoqTextCommand('aboutCursor', (editor) => launchQuery(editor, "about"));
    registerVscoqTextCommand('checkCursor', (editor) => launchQuery(editor, "check"));
    registerVscoqTextCommand('locateCursor', (editor) => launchQuery(editor, "locate"));
    registerVscoqTextCommand('printCursor', (editor) => launchQuery(editor, "print"));
    registerVscoqTextCommand('interpretToPoint', (editor) => sendInterpretToPoint(editor, client));
    registerVscoqTextCommand('interpretToEnd', (editor) => sendInterpretToEnd(editor, client));
    registerVscoqTextCommand('stepForward', (editor) => sendStepForward(editor, client));
    registerVscoqTextCommand('stepBackward', (editor) => sendStepBackward(editor, client));
    registerVscoqTextCommand('displayGoals', (editor) => {
        const reqParams = makeExecutionUpdateProofViewRequestParams(editor);
        GoalPanel.refreshGoalPanel(context.extensionUri, editor, client, reqParams);
    });
    registerVscoqTextCommand('documentState', async (editor) => {
            
        documentStateProvider.setDocumentUri(editor.document.uri);

        const document = await workspace.openTextDocument(documentStateProvider.uri);

        documentStateProvider.fire();

        await window.showTextDocument(document, {
            viewColumn: ViewColumn.Two,
            preserveFocus: true,
        }); 
        
    });

	client.onReady()
	.then(() => {

        checkVersion(client, context);

		initializeDecorations(context);
        
        // I think vscode should handle this automatically, TODO: try again after implemeting client capabilities
        context.subscriptions.push(workspace.onDidChangeConfiguration(event => updateServerOnConfigurationChange(event, context, client)));
		
        client.onNotification("vscoq/updateHighlights", ({uri, parsedRange, processingRange, processedRange}) => {
            client.saveHighlights(uri, parsedRange, processingRange, processedRange);
            client.updateHightlights();
		});

        client.onNotification("vscoq/searchResult", (searchResult: SearchCoqResult) => {
            searchProvider.renderSearchResult(searchResult);
        });

        let goalsHook = window.onDidChangeTextEditorSelection(
            (evt: TextEditorSelectionChangeEvent) => {                    
                const reqParams = makeCursorPositionUpdateProofViewRequestParams(evt);
                if(reqParams !== null) {
                    GoalPanel.refreshGoalPanel(context.extensionUri, evt.textEditor, client, reqParams);
                }
            }
        );

        window.onDidChangeActiveTextEditor(editor => {
            client.updateHightlights();
        });

	});


	// Start the client. This will also launch the server
	client.start();
    context.subscriptions.push(client);

}

// This method is called when your extension is deactivated
export function deactivate() {}
