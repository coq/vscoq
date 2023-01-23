import * as vscode from 'vscode';

export default class GoalProvider implements vscode.Disposable {

    public static readonly viewType = 'vscoq.goals'; 

    private _view?: vscode.WebviewPanel; 

    constructor(
        private _context: vscode.ExtensionContext,
    ){
        vscode.commands.registerTextEditorCommand('coq.displayGoals', (editor) => this.openGoalView(editor));
    }

    dispose(): void {
    
    }

    private openGoalView(editor: vscode.TextEditor) {
        let column = editor && editor.viewColumn ? editor.viewColumn + 1 : vscode.ViewColumn.Two;
        if (column === 4) { column = vscode.ViewColumn.Three; }
        if (this._view) {
            this._view.reveal(column, true);
        } else {
            const webviewPanel = vscode.window.createWebviewPanel('coq', 'Coq Goals',
                { viewColumn: column, preserveFocus: true },
                {
                    enableFindWidget: true,
                    retainContextWhenHidden: true,
                    enableScripts: true,
                    enableCommandUris: true,
                }); 
            //TODO: WILL NEED TO CONNECT THE API TO THE WEBVIEW HERE I PRESUME
            this._view = webviewPanel;
            webviewPanel.webview.html = this.initialHtml();
        }
    }
    

    private initialHtml() {
        
        const styleUri = vscode.Uri.joinPath(this._context.extensionUri, "media", "style.css");
    
        return `<!DOCTYPE html>
                    <html lang="en">
                        <head>
                            <meta charset="UTF-8">
                            <meta name="viewport" content="width=device-width, initial-scale=1.0">

                            <link href="${styleUri}" rel="stylesheet">
                            <title>Goals</title>
                        </head>
                        <body>

                        </body>
                    </html>`;
    }
    
}
