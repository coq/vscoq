import { getVSCodeDownloadUrl } from '@vscode/test-electron/out/util';
import * as path from 'path';
import {workspace, window, ExtensionContext, Range} from 'vscode';
import Client from './client';
import {initializeDecorations} from './Decorations'

import {
  LanguageClientOptions,
  ServerOptions,
} from 'vscode-languageclient/node';

let client: Client;


export function activate(context: ExtensionContext) {

	const config = workspace.getConfiguration('vscoq');

	let serverOptions: ServerOptions = {
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
	});

	// Start the client. This will also launch the server
	context.subscriptions.push(
		client.start(),
	);

}

// This method is called when your extension is deactivated
export function deactivate() {}
