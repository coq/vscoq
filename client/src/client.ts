import * as vscode from 'vscode';

import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions
} from 'vscode-languageclient/node';

import {decorationsManual, decorationsContinuous} from './Decorations';

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

    dispose(): void {

    };

    public handleHighlights(uri: String, parsedRange: vscode.Range[], processingRange: vscode.Range[], processedRange: vscode.Range[]) {
        const editors = this.getDocumentEditors(uri);
        
        const config = vscode.workspace.getConfiguration('vscoq.proof');

        editors.map(editor => {/* 
            editor.setDecorations(decorations.parsed, parsedRange);
            editor.setDecorations(decorations.processing, processingRange); */
            editor.setDecorations(
                config.mode === 0 
                ? decorationsManual.processed 
                : decorationsContinuous.processed, 
                processedRange
            );

        });
    }

    private getDocumentEditors(uri: String) {
        return vscode.window.visibleTextEditors.filter(editor => {
            return editor.document.uri.toString() === uri;
        });
    }

}
