import { getVSCodeDownloadUrl } from '@vscode/test-electron/out/util';
import {workspace, window, commands, ExtensionContext,
  TextEditorSelectionChangeEvent,
  TextEditorSelectionChangeKind, Range} from 'vscode';
import Client from './client';
import {initializeDecorations} from './Decorations';
import GoalPanel from './panels/GoalPanel';

import {
  LanguageClientOptions,
  ServerOptions,
} from 'vscode-languageclient/node';

let client: Client;


export function activate(context: ExtensionContext) {

	const config = workspace.getConfiguration('vscoq');

    // const goals = new GoalProvider(context);

    // context.subscriptions.push(goals);


    const displayGoals = commands.registerTextEditorCommand('coq.displayGoals', (editor) => {
		GoalPanel.render(editor, context.extensionUri);
	});


	context.subscriptions.push(displayGoals);

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

	client.onReady()
	.then(() => {
		initializeDecorations(context);
		client.onNotification("vscoq/updateHighlights", ({uri, parsedRange, processingRange, processedRange}) => {
            client.handleHighlights(uri, parsedRange, processingRange, processedRange);
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

}

// This method is called when your extension is deactivated
export function deactivate() {}
