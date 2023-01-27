import {workspace, window, commands, ExtensionContext,
  TextEditorSelectionChangeEvent,
  TextEditorSelectionChangeKind,
} from 'vscode';

import {
  LanguageClientOptions,
  ServerOptions,
} from 'vscode-languageclient/node';

import Client from './client';
import {initializeDecorations} from './Decorations';
import GoalPanel from './panels/GoalPanel';
import SearchViewProvider from './panels/SearchViewProvider';
import { SearchCoqResult } from './protocol/types';


let client: Client;

export function activate(context: ExtensionContext) {

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
	};

	// Create the language client and start the client.
	client = new Client(
		serverOptions,
		clientOptions
	);

    //register the search view provider 
    const searchProvider = new SearchViewProvider(context.extensionUri, client);
    context.subscriptions.push(window.registerWebviewViewProvider(SearchViewProvider.viewType, searchProvider));

    //register the command opening the goal view
    const displayGoals = commands.registerTextEditorCommand('coq.displayGoals', (editor) => {
		GoalPanel.render(editor, context.extensionUri);
	});
	context.subscriptions.push(displayGoals);

	client.onReady()
	.then(() => {
		initializeDecorations(context);
		
        client.onNotification("vscoq/updateHighlights", ({uri, parsedRange, processingRange, processedRange}) => {
            client.handleHighlights(uri, parsedRange, processingRange, processedRange);
		});

        client.onNotification("vscoq/searchResult", (searchResult: SearchCoqResult) => {
            searchProvider.renderSearchResult(searchResult);
        });

        let goalsHook = window.onDidChangeTextEditorSelection(
            (evt: TextEditorSelectionChangeEvent) => {

                if (evt.textEditor.document.languageId !== "coq") { return; };

                if (evt.kind === TextEditorSelectionChangeKind.Mouse || evt.kind === TextEditorSelectionChangeKind.Keyboard) {
                    
                    if(!GoalPanel.currentPanel) {commands.executeCommand('coq.displayGoals'); };
                    
                    GoalPanel.sendProofViewRequest(client, evt.textEditor.document.uri, 
                        evt.textEditor.document.version, evt.textEditor.selection.active);
                }
            }
        );


	});


	// Start the client. This will also launch the server
	client.start();
    context.subscriptions.push(client);

}

// This method is called when your extension is deactivated
export function deactivate() {}
