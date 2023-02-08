import { CancellationToken, CompletionContext, CompletionItem, CompletionItemProvider, CompletionList, MarkdownString, Position, ProviderResult, TextDocument, Uri } from "vscode";
import { CompletionItemKind, RequestType, VersionedTextDocumentIdentifier } from "vscode-languageclient/node";
import Client from "../client";
import { CompletionItemCoq, CompletionItemCoqRequest, CompletionItemCoqResponse, UpdateProofViewResponse } from "../protocol/types";


export default class LemmaCompletionProvider implements CompletionItemProvider<CompletionItem> {
    client: Client;

    constructor(client: Client) {
        this.client = client;
    }

    async provideCompletionItems(document: TextDocument, position: Position, token: CancellationToken, context: CompletionContext): Promise<CompletionItem[] | CompletionList<CompletionItem>> {
        let items = await this.sendCompletionItemsRequest(document.uri, document.version, position);
        return items.map(item => ({
            label: item.label, 
            documentation: new MarkdownString()
                .appendCodeblock(`${item.label}: ${item.typeString}`, "coq")
                .appendText(`Path: ${item.path}`),
            kind: CompletionItemKind.Function
        }) satisfies CompletionItem );
    }

    async resolveCompletionItem?(item: CompletionItem, token: CancellationToken): Promise<CompletionItem> {
        return item;
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