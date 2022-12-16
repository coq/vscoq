import { getVSCodeDownloadUrl } from '@vscode/test-electron/out/util';
import * as path from 'path';
import {workspace, window, ExtensionContext} from 'vscode';
import Client from './client'

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

	// Start the client. This will also launch the server
	client.start();
}

// This method is called when your extension is deactivated
export function deactivate() {}
