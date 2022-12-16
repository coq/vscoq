import { getVSCodeDownloadUrl } from '@vscode/test-electron/out/util';
import * as path from 'path';
import {workspace, window, ExtensionContext} from 'vscode';

import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind
} from 'vscode-languageclient/node';

let client: LanguageClient;

export function activate(context: ExtensionContext) {

	const message1 = "Starting vscoq !";
	window.showInformationMessage(message1);
	console.log("Hello !");

	const config = workspace.getConfiguration('vscoq');

	console.log("CONFIG", config.path, config.args);

	let serverOptions: ServerOptions = {
		command: config.path,
		args: config.args
	};

	let clientOptions: LanguageClientOptions = {
		documentSelector: [{ scheme: 'file', language: 'coq' }],
	};

	// Create the language client and start the client.
	client = new LanguageClient(
		'vscoq-language-server',
		'Coq Language Server',
		serverOptions,
		clientOptions
	);

	// Start the client. This will also launch the server
	client.start();

	const message = "Started vscoq !";
	window.showInformationMessage(message);
}

// This method is called when your extension is deactivated
export function deactivate() {}
