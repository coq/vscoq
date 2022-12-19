import * as vscode from 'vscode';

import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions
} from 'vscode-languageclient/node';

import {decorations} from './Decorations';

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
        );
		this._channel.appendLine("vscoq initialised");
	}

    public handleHighlights(uri: String, parsedRange: vscode.Range[], processingRange: vscode.Range[], processedRange: vscode.Range[]) {
        this._channel.appendLine("RECIEVED HIGHLIGHT INSTRUCTION");
        this._channel.appendLine(uri);
        const editors = this.getDocumentEditors(uri);

        editors.map(editor => {
            editor.setDecorations(decorations.parsed, parsedRange);
            editor.setDecorations(decorations.processing, processingRange);
            editor.setDecorations(decorations.processed, processedRange);
        });
    }

    private getDocumentEditors(uri: String) {
        return vscode.window.visibleTextEditors.filter(editor => {
            return editor.document.uri.toString() === uri;
        });
    }

}
