'use strict';

import * as vscode from 'vscode'

import * as view from './CoqView'
export {CoqView} from './CoqView'
import * as proto from './protocol'


export class SimpleCoqView implements view.CoqView {
  private out: vscode.OutputChannel;
  public onresize: (columns: number) => Thenable<void> = null;

  constructor(uri: string) {
    const name = uri + " - CoqTop";
    this.out = vscode.window.createOutputChannel(name);
    this.out.show(vscode.ViewColumn.Three);
  }

  dispose() {
    this.out.dispose();
  }

  private displayError(state: proto.CoqTopGoalResult) {
    this.out.appendLine(state.error.message);
  }

  private displayProof(state: proto.CoqTopGoalResult) {
    let out = "";
    if (view.countAllGoals(state) == 0) {
      out = "No more subgoals.";
    } else if (state.goals) {
      if(state.goals.length > 0) {
        state.goals[0].hypotheses.forEach((hyp) =>
          out = out + hyp + '\n');
        state.goals.forEach((g,i) => {
          out = out + `----------------------(${i+1}/${state.goals.length})\n${g.goal}\n`;
        })
        
      } else
        out = "There unfocused goals.";
    }
    this.out.append(out);
  }

  private displayTop(state: proto.CoqTopGoalResult) {

  }

  public update(state: proto.CoqTopGoalResult) {
    this.out.clear();
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