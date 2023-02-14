import { pathToFileURL } from "url";
import { CancellationToken, Declaration, DeclarationProvider, Location, Position, ProviderResult, TextDocument, Uri } from "vscode";
import { RequestType, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import Client from "./client";
import { DeclarationLocationCoqRequest, DeclarationLocationCoqResponse } from "./protocol/types";
import { existsSync } from 'fs';

export default class DecProvider implements DeclarationProvider {
    client: Client;
    
    constructor(client: Client) {
        this.client = client;
    }

    async provideDeclaration(document: TextDocument, position: Position, token: CancellationToken): Promise<Declaration> {
        let coqIdentRegex = /(\.?(\w|\_)(\w|\d|\_|\')*)+/;
        let wordRange = document.getWordRangeAtPosition(position, coqIdentRegex);
        let requestedDeclaration = document.getText(wordRange);
        let response = await this.sendDeclarationLocationRequest(document.uri, document.version, position, requestedDeclaration);
        let path = response.path.replace(/\.vo$/, ".v");
        if (path && existsSync(path)) {
            return new Location(Uri.parse(path), new Position(0, 0));
        }
        throw new Error(`Could not find path to ${requestedDeclaration}`);
    }

    private sendDeclarationLocationRequest(uri: Uri, version: number, position: Position, requestedDeclaration: string): Promise<DeclarationLocationCoqResponse> {
        const req = new RequestType<DeclarationLocationCoqRequest, DeclarationLocationCoqResponse, void>("vscoq/declarationLocation");
        let textDocument = VersionedTextDocumentIdentifier.create(
            uri.toString(),
            version
        );
        const params: DeclarationLocationCoqRequest = { textDocument, position, requestedDeclaration };
        return this.client.sendRequest(req, params).then(
            (response: DeclarationLocationCoqResponse) => {
                return response;
            }
        );
    }
}