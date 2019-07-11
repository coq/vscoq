'use strict';

import * as vscode from 'vscode'
import * as fs from 'fs'

import * as view from './CoqView'
export {CoqView} from './CoqView'
import * as proto from './protocol'

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

export class MDCoqView implements view.CoqView {
  private editor: vscode.TextEditor;
  private outDoc: vscode.TextDocument;
  private docUri: vscode.Uri;
  private filename : string;
  private visible = false;
  private resizeEvent = new vscode.EventEmitter<number>();

  constructor(uri: vscode.Uri) {
    this.docUri = uri;
    this.createBuffer();
  }

  public get resize() { return this.resizeEvent.event };
  
  private async createBuffer() {
    try {
      this.filename = this.docUri.fsPath + ".view.md";
      fs.close(await createFile(this.filename));
      
      
      const focusedDoc = vscode.window.activeTextEditor ? vscode.window.activeTextEditor.document : null;
      this.outDoc = await vscode.workspace.openTextDocument(this.filename);
      
    
      // vscode.window.onDidChangeActiveTextEditor((editor) => {
      //   var a = editor.document;
      // });
      
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
    this.editor.hide();
    fs.unlink(this.filename);
  }
  

  private displayError(state: proto.CommandResult) {
    // this.out.appendLine(state.error.message);
  }
  
  private async setOutputText(text: string) {
    await writeFile(this.filename, text);
    await this.refreshView();
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

  private displayProof(state: proto.CommandResult) {
    let out = "";
    if (view.countAllGoals(state) == 0) {
      out = "No more subgoals.";
    } else if (state.type === 'proof-view') {
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

  

  private async refreshView() {
    const focusedDoc = vscode.window.activeTextEditor ? vscode.window.activeTextEditor.document : null;
    await vscode.window.showTextDocument(this.editor.document,vscode.ViewColumn.Two);
    // vscode.commands.executeCommand('workbench.action.markdown.togglePreview');
    // await vscode.commands.executeCommand('workbench.action.markdown.togglePreview');
    await vscode.commands.executeCommand('workbench.action.markdown.togglePreview');
    if(focusedDoc)
      vscode.window.showTextDocument(focusedDoc);    
  }

  public async update(state: proto.CommandResult) {
    switch (view.getDisplayState(state)) {
      case view.DisplayState.Error:
        this.displayError(state);
        break;
      case view.DisplayState.Proof:
        this.displayProof(state);
        break;
    }
  }
  
  public async show() {
    this.visible = true;
    await vscode.window.showTextDocument(this.editor.document,vscode.ViewColumn.Two);
  }

  public showExternal() : Promise<void> {
    return Promise.reject('external view is unsupported');
  }

  public isVisible() : boolean {
    return this.visible;
  }

}