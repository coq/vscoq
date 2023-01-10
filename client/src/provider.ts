import * as vscode from 'vscode';

export default class GoalProvider implements vscode.WebviewViewProvider {

    public static readonly viewType = 'vscoq.goals'; 

    private _view?: vscode.WebviewView; 

    constructor(
        private readonly _extensionUri: vscode.Uri,
    ){
        
    }

    public resolveWebviewView(
        webviewView: vscode.WebviewView,
        context: vscode.WebviewViewResolveContext,
        _token: vscode.CancellationToken,
    ) {
        this._view = webviewView;

        webviewView.webview.options = {
            enableScripts: false,
        };

        webviewView.webview.html = this._getHtmlForWebview(webviewView.webview);

    }
    

    private _getHtmlForWebview(webview: vscode.Webview) {
        
        const styleUri = vscode.Uri.joinPath(this._extensionUri, "media", "style.css");
    
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
