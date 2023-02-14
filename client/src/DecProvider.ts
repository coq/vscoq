import { pathToFileURL } from "url";
import { CancellationToken, Declaration, DeclarationProvider, Location, Position, ProviderResult, TextDocument, Uri } from "vscode";
import { RequestType, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import Client from "./client";
import { CompletionItemCoq, CompletionItemCoqRequest, CompletionItemCoqResponse } from "./protocol/types";

export default class DecProvider implements DeclarationProvider {
    client: Client;
    coqlibPath: URL | undefined;
    
    constructor(client: Client, coqlibPath : string) {
        this.client = client;
        this.coqlibPath = coqlibPath ? pathToFileURL(coqlibPath) : undefined; 
    }

    async provideDeclaration(document: TextDocument, position: Position, token: CancellationToken): Promise<Declaration> {
        if (!this.coqlibPath) {
            throw new Error("No path set to CoqLib");
        }
        let coqIdentRegex = /(\.?(\w|\_)(\w|\d|\_|\')*)+/;
        let wordRange = document.getWordRangeAtPosition(position, coqIdentRegex);
        let word = document.getText(wordRange);
        let items = await this.sendCompletionItemsRequest(document.uri, document.version, position);
        let item = items.find((i) => i.label === word);
        let pathItems = item?.path?.split('.');
        let filename = item?.path?.split('.').at(-1) + ".v";
        let path = this.coqlibPath + `/theories/` + pathItems?.slice(1, -1).concat([filename]).join("/");
        return new Location(Uri.parse(path), new Position(0, 0));
    }

    private sendCompletionItemsRequest(uri: Uri, version: number, position: Position): Promise<CompletionItemCoq[]> {
        const req = new RequestType<CompletionItemCoqRequest, CompletionItemCoqResponse, void>("vscoq/getCompletionItems");
        let textDocument = VersionedTextDocumentIdentifier.create(
            uri.toString(),
            version
        );
        const params: CompletionItemCoqRequest = { textDocument, position };
        return this.client.sendRequest(req, params).then(
            (completionItemCoqResponse: CompletionItemCoqResponse) => {
                return completionItemCoqResponse.completionItems;
            }
        );
    }
}