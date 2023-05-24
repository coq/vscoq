import { Disposable, Webview, WebviewPanel, window, workspace, Uri, ViewColumn, TextEditor, TextDocumentContentProvider, CancellationToken, ProviderResult } from "vscode";
import { UpdateProofViewRequest, UpdateProofViewResponse, } from '../protocol/types';
import {
  RequestType,
  TextDocumentIdentifier,
} from "vscode-languageclient";

import { DocumentStateRequest, DocumentStateResponse } from "../protocol/types";

import Client from '../client';

export class DocumentStateViewProvider implements TextDocumentContentProvider {

    readonly scheme = "vscoq-document-state";
    readonly uri = Uri.parse(this.scheme + "://doc");

    constructor(
        private _client: Client
    ){ }

    async provideTextDocumentContent(uri: Uri, token: CancellationToken): Promise<string> {
        const textDocument = TextDocumentIdentifier.create(uri.toString());
        const params: DocumentStateRequest = {textDocument}; 
        const req = new RequestType<DocumentStateRequest, DocumentStateResponse, void>("vscoq/documentState");
        return this._client.sendRequest(req, params).then(
            (result: DocumentStateResponse) => {
                return result.document;
            }
        );   
    }

}