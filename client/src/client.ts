import * as vscode from 'vscode';

import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from 'vscode-languageclient/node';

export default class Client extends LanguageClient {

	private _channel: any = vscode.window.createOutputChannel('vscoq');

	constructor(
        serverOptions: ServerOptions,
        clientOptions: LanguageClientOptions,
	) {
        super(
		    'vscoq-language-server',
		    'Coq Language Server',
		    serverOptions,
		    clientOptions
        )
		this._channel.appendLine("vscoq commands initialised");
	}

}
