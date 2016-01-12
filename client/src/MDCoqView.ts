'use strict';

import * as vscode from 'vscode'
import * as fs from 'fs'

import * as view from './CoqView'
export {CoqView} from './CoqView'
import * as proto from './protocol'
import * as textUtil from './text-util'

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

function edit(editor: vscode.TextEditor) : Promise<vscode.TextEditorEdit> {
  return new Promise<vscode.TextEditorEdit>((resolve) => {
    editor.edit(resolve);
  });
}

export class MDCoqView implements view.CoqView {
  private editor: vscode.TextEditor;
  private outDoc: vscode.TextDocument;
  private docUri: vscode.Uri;
  private outFile: number; // file descriptor
  private currentPos = new vscode.Position(0,0);

  constructor(uri: vscode.Uri) {
    this.docUri = uri;
    this.createBuffer();
  }
  
  private async createBuffer() {
    try {
      const name = this.docUri.fsPath + ".view.md";
      fs.close(await createFile(name));
      
      const focusedEditor = vscode.window.activeTextEditor;
      this.outDoc = await vscode.workspace.openTextDocument(name);
      this.editor = vscode.window.visibleTextEditors.find((e) => e.document === this.outDoc);
      if(!this.editor)
        this.editor = await vscode.window.showTextDocument(this.outDoc, vscode.ViewColumn.Three);
      else
        this.editor.show(vscode.ViewColumn.Three);
      vscode.commands.executeCommand('workbench.action.markdown.togglePreview');
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
  }

  private displayError(state: proto.CoqTopGoalResult) {
    // this.out.appendLine(state.error.message);
  }
  
  private setOutputText(text: string) {
    this.editor.edit((eb) => {
      // eb.delete(new vscode.Range(0,0,2,0));
      // eb.insert(new vscode.Position(0,0), text);
      // eb.replace(new vscode.Range(0,0,this.outDoc.lineCount,0), text);
      eb.replace(new vscode.Range(0,0,0,this.outDoc.getText().length), text);
      // const focusedEditor = vscode.window.activeTextEditor;
      // this.editor.show();
      // vscode.commands.executeCommand('workbench.action.markdown.togglePreview');
      // vscode.commands.executeCommand('workbench.action.markdown.togglePreview');
      // if(focusedEditor)
        // focusedEditor.show();
    })
  }

  private displayProof(state: proto.CoqTopGoalResult) {
    let out = "";
    if (view.countAllGoals(state) == 0) {
      out = "No more subgoals.";
    } else if (state.goals) {
      if(state.goals.length > 0) {
        state.goals[0].hypotheses.forEach((hyp) =>
          out = out + hyp + '<br/>');
        out = out + "<hr/>";
        out = out + state.goals[0].goal + "<br/>";
        
      } else
        out = "There unfocused goals.";
    }
    this.setOutputText(out);
  }

  private displayTop(state: proto.CoqTopGoalResult) {
    this.editor.edit((eb) => {
      eb.replace(new vscode.Range(0,0,this.outDoc.lineCount,0), "Top");
    })
    // const eb = await edit(this.editor);
    // eb.insert(new vscode.Position(0,0), "Hello World");
  }

  public update(state: proto.CoqTopGoalResult) {
    switch (view.getDisplayState(state)) {
      case view.DisplayState.Error:
        this.displayError(state);
        break;
      case view.DisplayState.Proof:
        this.displayProof(state);
        break;
    }
  }
  
}