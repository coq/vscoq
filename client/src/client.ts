import * as vscode from 'vscode';

import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  integer
} from 'vscode-languageclient/node';

import {decorationsManual, decorationsContinuous} from './Decorations';

import { FeedbackChannel } from './protocol/types';

export default class Client extends LanguageClient {

	private _channel: any = vscode.window.createOutputChannel('vscoq');
    private _debug: any = vscode.window.createOutputChannel('Debug');
    private _notice: any = vscode.window.createOutputChannel('Notice');
    private _info: any = vscode.window.createOutputChannel('Info');
    private _decorations: Map<String, vscode.Range[]> = new Map<String, vscode.Range[]>();

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
        this._channel.dispose();
        this._debug.dispose();
        this._info.dispose();
        this._notice.dispose();
    };

    public writeToVscoq2Channel(message: string) {
        this._channel.appendLine(message);
    }

    public writeToFeedbackChannel(channel: integer, message: string) {
        if(channel === FeedbackChannel.debug) {
            this._debug.appendLine(message);
        }
        if(channel === FeedbackChannel.info) {
            this._info.appendLine(message);
        }
        if(channel === FeedbackChannel.notice) {
            this._notice.appendLine(message);
        }
    };

    public saveHighlights(uri: String, parsedRange: vscode.Range[], processingRange: vscode.Range[], processedRange: vscode.Range[]) {
        this._decorations.set(uri, processedRange);
    }

    public updateHightlights() {
        for(let entry of this._decorations.entries()) {
            this.updateDocumentEditors(entry[0], entry[1]);
        }
    };

    private getDocumentEditors(uri: String) {
        return vscode.window.visibleTextEditors.filter(editor => {
            return editor.document.uri.toString() === uri;
        });
    }

    private updateDocumentEditors(uri: String, ranges: vscode.Range[]) {
        const config = vscode.workspace.getConfiguration('vscoq.proof');
        const editors = this.getDocumentEditors(uri);
        editors.map(editor => {
            if(config.mode === 0) {
                editor.setDecorations(decorationsManual.processed, ranges);
            } else {
                editor.setDecorations(decorationsContinuous.processed, ranges);
            }
        });
    }

}
