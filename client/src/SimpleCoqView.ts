'use strict';

import * as vscode from 'vscode'

import * as view from './CoqView'
export {CoqView} from './CoqView'
import * as proto from './protocol'
import * as psm from './prettify-symbols-mode';


export class SimpleCoqView implements view.CoqView {
  private visible = false;
  private out: vscode.OutputChannel;
  private resizeEvent = new vscode.EventEmitter<number>();

  constructor(uri: string) {
    const name = uri + " - CoqTop";
    this.out = vscode.window.createOutputChannel(name);
    this.out.show(vscode.ViewColumn.Three);
  }

  public get resize() { return this.resizeEvent.event; }

  dispose() {
    this.out.dispose();
  }

  private displayError(state: proto.FailureResult) {
    this.out.appendLine(psm.prettyTextToString(state.message));
  }

  private displayProof(state: proto.CommandResult) {
    let out = "";
    if (view.countAllGoals(state) == 0) {
      out = "No more subgoals.";
    } else if (state.type === 'proof-view') {
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

  public update(state: proto.CommandResult) {
    this.out.clear();
    if(state.type === 'failure')
        this.displayError(state);
    else if(state.type === 'proof-view')
      this.displayProof(state);
  }

  public async show() {
    this.visible = true;
    await this.out.show(vscode.ViewColumn.Two,true);
  }

  public showExternal() : Promise<void> {
    return Promise.reject('external view is unsupported');
  }

  public isVisible() : boolean {
    return this.visible;
  }

}