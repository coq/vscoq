import { getVSCodeDownloadUrl } from '@vscode/test-electron/out/util';
import {workspace, window, commands, ExtensionContext,
  TextEditorSelectionChangeEvent,
  TextEditorSelectionChangeKind,
  TextEditor,
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

    const launchQuery = (editor: TextEditor, type: string)=> {
        const selection = editor.selection;
        const {end, start} = selection; 
        if(end.line !== start.line) {return;} //don't allow for multiline selections
        //either use the user selection or if no selection than infer the word under the cursor
        const wordAtCurorRange = (end.character !== start.character) ? selection : editor.document.getWordRangeAtPosition(end);
        if(!wordAtCurorRange) {return; } //there is no word: do nothing
        const queryText = editor.document.getText(wordAtCurorRange);
        //focus on the query panel
        commands.executeCommand('coq.search.focus');
        //launch the query
        searchProvider.launchQuery(queryText, type);
    };

    const searchCursor = commands.registerTextEditorCommand('coq.searchCursor', (editor) => {
        launchQuery(editor, "Search");
        });
    context.subscriptions.push(searchCursor);

    const aboutCursor = commands.registerTextEditorCommand('coq.aboutCursor', (editor) => {
        launchQuery(editor, "About");
    });
    context.subscriptions.push(aboutCursor);

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
