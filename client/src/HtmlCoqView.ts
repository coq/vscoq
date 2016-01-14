'use strict';
import * as vscode from 'vscode'
import * as fs from 'fs'

import * as view from './CoqView'
export {CoqView} from './CoqView'
import * as proto from './protocol'
import * as textUtil from './text-util'
import * as WebSocket from 'ws';
import * as http from 'http';
import * as path from 'path';


function createFile(path: string) : Promise<number> {
  return new Promise<number>((resolve,reject) => {
    fs.open(path, 'w', (err: any, fd: number) => {
      if(err)
        reject(err)
      else
        resolve(fd);
    } );
  })
}

function writeFile(filename: string, data: any) : Promise<void> {
  return new Promise<void>((resolve,reject) => {
    fs.writeFile(filename, data, {encoding: 'utf8'}, (err: NodeJS.ErrnoException) => {
      if(err)
        reject(err)
      else
        resolve();
    } );
  })
}

function edit(editor: vscode.TextEditor) : Promise<vscode.TextEditorEdit> {
  return new Promise<vscode.TextEditorEdit>((resolve) => {
    editor.edit(resolve);
  });
}

/**
 * Displays a Markdown-HTML file which contains javascript to connect to this view
 * and update the goals and show other status info
 */
export class HtmlCoqView implements view.CoqView {
  private editor: vscode.TextEditor;
  private outDoc: vscode.TextDocument;
  private docUri: vscode.Uri;
  private outFile: number; // file descriptor
  private mdFilename : vscode.Uri;
  private server : WebSocket.Server;
  private httpServer : http.Server;
  // private connection : Promise<WebSocket>;
  private serverReady : Promise<void>;
  private currentState : proto.CoqTopGoalResult = {}; 

  constructor(uri: vscode.Uri) {
    this.docUri = uri;
    
    const httpServer = this.httpServer = http.createServer();
    this.serverReady = new Promise<void>((resolve, reject) =>
      httpServer.listen(0,'localhost',undefined,(e) => {
        if(e)
          reject(e)
        else
          resolve();
      }));
    
    this.server = new WebSocket.Server({server: httpServer});
    
    this.server.on('connection', (ws: WebSocket) => {
      ws.send(JSON.stringify(this.currentState));
    })

    this.createBuffer();
  }
  
  private async createBuffer() : Promise<void> {
    try {
      await this.serverReady;
      const serverAddress = this.httpServer.address();

      this.mdFilename = vscode.Uri.file(this.docUri.fsPath + ".view.md");
      const templateFileName = vscode.Uri.file(__dirname + '/HtmlView/Coq.html').toString().replace(/%3A/, ':');
      await writeFile(this.mdFilename.fsPath,
`<div style="margin:0px;padding:0px;width:100%;height:100vh;border:none;position:absolute;top:0px;left:0px;right:0px;bottom:0px">
<iframe src="${templateFileName}?host=${serverAddress.address}&port=${serverAddress.port}" seamless style="position:absolute;top:0px;left:0px;right:0px;bottom:0px;border:none;margin:0px;padding:0px;width:100%;height:100%" />
</div>`);


      const focusedDoc = vscode.window.activeTextEditor ? vscode.window.activeTextEditor.document : null;
      this.outDoc = await vscode.workspace.openTextDocument(this.mdFilename);
      this.editor = await vscode.window.showTextDocument(this.outDoc, vscode.ViewColumn.Two);
      await vscode.commands.executeCommand('workbench.action.markdown.togglePreview');
      if(focusedDoc)
        vscode.window.showTextDocument(focusedDoc);
      // if(focusedEditor)
      //   focusedEditor.show();

      // const eb = await edit(this.editor);
      // eb.insert(new vscode.Position(1,1), "Hello World");
      // this.write(eb, "He\nllo");
      // this.write(eb, "W\norld\n!!!!");
      // const s = await vscode.commands.getCommands();
      // s.forEach((x) => )
    } catch(err) {
      vscode.window.showErrorMessage(err.toString());
    }    
  }
  
//   private write(eb: vscode.TextEditorEdit, text: string) {
//     eb.insert(this.currentPos, text);
//     const delta = textUtil.positionAt(text, text.length);
//     this.currentPos = this.currentPos.translate(delta.line, delta.character);
//   }
// 
//   private writeLine(eb: vscode.TextEditorEdit, text: string) {
//     this.write(eb, text + '\n');
//   }


  dispose() {
    fs.unlinkSync(this.mdFilename.fsPath);
    this.editor.hide();
  }
  

  private async setOutputText(text: string) {
    // for(const connection of this.server.clients) {
    //   if(connection.send())
    // }
    // const connection = await this.connection;
    // connection.send(text);
    // this.editor.edit((eb) => {
    //   // eb.delete(new vscode.Range(0,0,2,0));
    //   // eb.insert(new vscode.Position(0,0), text);
    //   // eb.replace(new vscode.Range(0,0,this.outDoc.lineCount,0), text);
    //   eb.replace(new vscode.Range(0,0,0,this.outDoc.getText().length), text);
    //   // const focusedEditor = vscode.window.activeTextEditor;
    //   // this.editor.show();
    //   // vscode.commands.executeCommand('workbench.action.markdown.togglePreview');
    //   // vscode.commands.executeCommand('workbench.action.markdown.togglePreview');
    //   // if(focusedEditor)
    //     // focusedEditor.show();
    // })
  }

  private displayError(state: proto.CoqTopGoalResult) {
    // this.out.appendLine(state.error.message);
  }
  
  private displayProof(state: proto.CoqTopGoalResult) {
    let out = "";
    if (view.countAllGoals(state) == 0) {
      out = "No more subgoals.";
    } else if (state.goals) {
      if(state.goals.length > 0) {
        state.goals[0].hypotheses.forEach((hyp) =>
          out = out + hyp + '<br/>');
        state.goals.forEach((g,i) => {
          out = out + `<hr/>(${i+1}/${state.goals.length})<br/>${g.goal}<br/>`;
        })
        
      } else
        out = "There unfocused goals.";
    }
    this.setOutputText(out);
  }

  private displayTop(state: proto.CoqTopGoalResult) {
    this.setOutputText("Top")
    // this.editor.edit((eb) => {
    //   eb.replace(new vscode.Range(0,0,this.outDoc.lineCount,0), "Top");
    // })
    // const eb = await edit(this.editor);
    // eb.insert(new vscode.Position(0,0), "Hello World");
  }

  public async update(state: proto.CoqTopGoalResult) {
    this.currentState = state;
    for(const connection of this.server.clients) {
      try {
      connection.send(JSON.stringify(state));
      } catch(error) {}
    }
    // switch (view.getDisplayState(state)) {
    //   case view.DisplayState.Error:
    //     this.displayError(state);
    //     break;
    //   case view.DisplayState.Proof:
    //     this.displayProof(state);
    //     break;
    // }
  }
  
}