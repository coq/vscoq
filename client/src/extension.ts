import {workspace, window, commands, ExtensionContext,
  TextEditorSelectionChangeEvent,
  TextEditorSelectionChangeKind,
  TextEditor,
  ViewColumn,
  TextEditorRevealType,
  Selection,
  Uri
} from 'vscode';

import {
  LanguageClientOptions,
  ServerOptions,
} from 'vscode-languageclient/node';

import Client from './client';
import { updateServerOnConfigurationChange } from './configuration';
import { checkVersion } from './utilities/versioning';
import {initializeDecorations} from './Decorations';
import GoalPanel from './panels/GoalPanel';
import SearchViewProvider from './panels/SearchViewProvider';
import {
    MoveCursorNotification, 
    ProofViewNotification, 
    SearchCoqResult
} from './protocol/types';
import { 
    sendInterpretToPoint,
    sendInterpretToEnd,
    sendStepForward,
    sendStepBackward
} from './manualChecking';
import { 
    makeVersionedDocumentId,
    isMouseOrKeyboardEvent
} from './utilities/utils';
import { DocumentStateViewProvider } from './panels/DocumentStateViewProvider';
import VsCoqToolchainManager, {ToolchainError, ToolChainErrorCode} from './utilities/toolchain';

let client: Client;

export function activate(context: ExtensionContext) {
    
    const coqTM = new VsCoqToolchainManager();
    coqTM.intialize().then(
        () => {
            const serverOptions = coqTM.getServerConfiguration(); 
            intializeExtension(serverOptions);
        }, 
        (err: ToolchainError) => {
            switch(err.status) {

                case ToolChainErrorCode.notFound: 
                    window.showErrorMessage(err.message, {title: "Install the VsCoq language server", id: 0}, {title: "Downgrade to VsCoq 0.3.9", id: 1})
                    .then(act => {
                        if(act?.id === 0) {
                            commands.executeCommand("vscode.open", Uri.parse('https://github.com/coq-community/vscoq#installing-the-language-server'));
                        }
                        if(act?.id === 1) {
                            commands.executeCommand("vscode.open", Uri.parse('https://github.com/coq-community/vscoq#problems-with-vscoq-2'));
                        }
                    });
                    break;

                case ToolChainErrorCode.launchError: 
                    window.showErrorMessage(err.message, {title: "Get Coq", id: 0}, {title: "Downgrade to VsCoq 0.3.9", id: 1})
                    .then(act => {
                        if(act?.id === 0) {
                            commands.executeCommand("vscode.open", Uri.parse('https://coq.inria.fr/download'));
                        }
                        if(act?.id === 1) {
                            commands.executeCommand("vscode.open", Uri.parse('https://github.com/coq-community/vscoq#problems-with-vscoq-2'));
                        }
                        
                    });
                    
            }
        }
    );

    function registerVscoqTextCommand(command: string, callback: (textEditor: TextEditor, ...args: any[]) => void) {
        context.subscriptions.push(commands.registerTextEditorCommand('extension.coq.' + command, callback));
    };
    
    function intializeExtension(serverOptions: ServerOptions) {
        const config = workspace.getConfiguration('vscoq');

        let clientOptions: LanguageClientOptions = {
            documentSelector: [{ scheme: 'file', language: 'coq' }],
            initializationOptions: config
        };

        // Create the language client and start the client.
        client = new Client(
            serverOptions,
            clientOptions
        );

        //register the search view provider 
        const searchProvider = new SearchViewProvider(context.extensionUri, client);
        context.subscriptions.push(window.registerWebviewViewProvider(SearchViewProvider.viewType, searchProvider));

        const documentStateProvider = new DocumentStateViewProvider(client); 
        context.subscriptions.push(workspace.registerTextDocumentContentProvider("vscoq-document-state", documentStateProvider));

        const launchQuery = (editor: TextEditor, type: string)=> {
            const selection = editor.selection;
            const {end, start} = selection; 
            if(end.line !== start.line) {return;} //don't allow for multiline selections
            //either use the user selection or if no selection than infer the word under the cursor
            const wordAtCurorRange = (end.character !== start.character) ? selection : editor.document.getWordRangeAtPosition(end);
            if(!wordAtCurorRange) {return; } //there is no word: do nothing
            const queryText = editor.document.getText(wordAtCurorRange);
            //focus on the query panel
            commands.executeCommand('vscoq.search.focus');
            //launch the query
            searchProvider.launchQuery(queryText, type);
        };

        registerVscoqTextCommand('query.search', (editor) => launchQuery(editor, "search"));
        registerVscoqTextCommand('query.about', (editor) => launchQuery(editor, "about"));
        registerVscoqTextCommand('query.check', (editor) => launchQuery(editor, "check"));
        registerVscoqTextCommand('query.locate', (editor) => launchQuery(editor, "locate"));
        registerVscoqTextCommand('query.print', (editor) => launchQuery(editor, "print"));
        registerVscoqTextCommand('addQueryTab', () => searchProvider.addTab());
        registerVscoqTextCommand('collapseAllQueries', () => searchProvider.collapseAll());
        registerVscoqTextCommand('expandAllQueries', () => searchProvider.expandAll());
        registerVscoqTextCommand('interpretToPoint', (editor) => sendInterpretToPoint(editor, client));
        registerVscoqTextCommand('interpretToEnd', (editor) => sendInterpretToEnd(editor, client));
        registerVscoqTextCommand('stepForward', (editor) => sendStepForward(editor, client));
        registerVscoqTextCommand('stepBackward', (editor) => sendStepBackward(editor, client));
        registerVscoqTextCommand('documentState', async (editor) => {
                
            documentStateProvider.setDocumentUri(editor.document.uri);

            const document = await workspace.openTextDocument(documentStateProvider.uri);

            documentStateProvider.fire();

            await window.showTextDocument(document, {
                viewColumn: ViewColumn.Two,
                preserveFocus: true,
            }); 
            
        });

        client.onReady()
        .then(() => {
            
            checkVersion(client, context);

            initializeDecorations(context);
            
            // I think vscode should handle this automatically, TODO: try again after implemeting client capabilities
            context.subscriptions.push(workspace.onDidChangeConfiguration(event => {
                updateServerOnConfigurationChange(event, context, client);
                if(event.affectsConfiguration('vscoq.proof.mode')) {
                    client.resetHighlights();
                    client.updateHightlights();
                }
            }));
            
            client.onNotification("vscoq/updateHighlights", (notification) => {
            
                client.saveHighlights(
                    notification.uri, 
                    notification.parsedRange, 
                    notification.processingRange, 
                    notification.processedRange
                );
            
                client.updateHightlights();
            });

            client.onNotification("vscoq/moveCursor", (notification: MoveCursorNotification) => {
                const {uri, range} = notification;
                const editors = window.visibleTextEditors.filter(editor => {
                    return editor.document.uri.toString() === uri.toString();
                });
                if(workspace.getConfiguration('vscoq.proof.cursor').sticky === true &&
                workspace.getConfiguration('vscoq.proof').mode === 0) {
                    editors.map(editor => {
                        editor.selections = [new Selection(range.end, range.end)];
                        editor.revealRange(range, TextEditorRevealType.Default);
                    });
                }
            });

            client.onNotification("vscoq/searchResult", (searchResult: SearchCoqResult) => {
                searchProvider.renderSearchResult(searchResult);
            });

            client.onNotification("vscoq/proofView", (proofView: ProofViewNotification) => {
                const editor = window.activeTextEditor ? window.activeTextEditor : window.visibleTextEditors[0];
                GoalPanel.proofViewNotification(context.extensionUri, editor, proofView);
            });

            let goalsHook = window.onDidChangeTextEditorSelection(
                (evt: TextEditorSelectionChangeEvent) => {                    
                    if (evt.textEditor.document.languageId === "coq" 
                        && workspace.getConfiguration('vscoq.proof').mode === 1
                        && isMouseOrKeyboardEvent(evt)) 
                    {
                        sendInterpretToPoint(evt.textEditor, client);
                    }
                }
            );

            window.onDidChangeActiveTextEditor(editor => {
                client.updateHightlights();
            });

        });

        // Start the client. This will also launch the server
        client.start();
        context.subscriptions.push(client);
    }	

}

// This method is called when your extension is deactivated
export function deactivate() {}
