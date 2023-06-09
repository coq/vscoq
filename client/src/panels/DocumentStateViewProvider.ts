import { 
    window, 
    Uri, 
    TextDocumentContentProvider, 
    CancellationToken, 
    EventEmitter,
    Event
} from "vscode";
import {
  RequestType,
  TextDocumentIdentifier,
} from "vscode-languageclient";

import { DocumentStateRequest, DocumentStateResponse } from "../protocol/types";

import Client from '../client';

export class DocumentStateViewProvider implements TextDocumentContentProvider {

    readonly scheme = "vscoq-document-state";
    readonly uri = Uri.parse(this.scheme + "://doc");

    private static _channel: any = window.createOutputChannel('vscoq-document-state-provider');
    private textDocument: TextDocumentIdentifier | null = null; 
    readonly eventEmitter = new EventEmitter<Uri>();

    constructor(
        private _client: Client
    ){ }

    fire() : void {
        if(this.uri !== null) {
            DocumentStateViewProvider._channel.appendLine("Firing event");
            DocumentStateViewProvider._channel.appendLine("Current doc uri: " + this.textDocument?.uri.toString());
            this.eventEmitter.fire(this.uri);
        } 
    }
    
    get onDidChange(): Event<Uri> {
        return this.eventEmitter.event;
    }

    setDocumentUri(uri: Uri) {
        this.textDocument = TextDocumentIdentifier.create(uri.toString());
    }

    async provideTextDocumentContent(uri: Uri, token: CancellationToken): Promise<string> {
    
        if(this.textDocument === null) {
            DocumentStateViewProvider._channel.appendLine("No document was set so no state can be returned !"); 
            return Promise.reject();
        }

        const params: DocumentStateRequest = {textDocument: this.textDocument}; 
        const req = new RequestType<DocumentStateRequest, DocumentStateResponse, void>("vscoq/documentState");
        DocumentStateViewProvider._channel.appendLine("Getting document state for uri: " + this.textDocument.uri.toString());
        return this._client.sendRequest(req, params).then(
            (result: DocumentStateResponse) => {
                //DocumentStateViewProvider._channel.appendLine("Recieved response: " + result.document);
                return result.document;
            }
        );   
    }

}