'use strict';

import * as vscode from 'vscode'

import * as proto from './protocol'

export enum DisplayState {
  Proof, Top, Error
}

export function getDisplayState(state: proto.CoqTopGoalResult) {
  if (state.error)
    return DisplayState.Error;
  if (state.goals || state.backgroundGoals || state.abandonedGoals || state.shelvedGoals)
    return DisplayState.Proof;
  else
    return DisplayState.Top;
}

function countUnfocusedGoalStack(u: proto.UnfocusedGoalStack) {
  if(u)
    return u.before.length + u.after.length + countUnfocusedGoalStack(u.next);
  else
    return 0;
}

export function countAllGoals(state: proto.CoqTopGoalResult): number {
  const result =
    (state.goals ? state.goals.length : 0)
    + countUnfocusedGoalStack(state.backgroundGoals)
    + (state.abandonedGoals ? state.abandonedGoals.length : 0)
    + (state.shelvedGoals ? state.shelvedGoals.length : 0);
  return result;
}

export function adjacentPane(pane: vscode.ViewColumn) : vscode.ViewColumn {
  switch (pane) {
  case vscode.ViewColumn.One: return vscode.ViewColumn.Two
  case vscode.ViewColumn.Two: return vscode.ViewColumn.Three;
  case vscode.ViewColumn.Three: return vscode.ViewColumn.Two;
  }
}

export interface CoqView extends vscode.Disposable {

  update(state: proto.CoqTopGoalResult) : void;
  // message(message: string) : void;
  onresize: (columns: number) => Thenable<void>;

  show(preserveFocus: boolean, pane: vscode.ViewColumn) : Promise<void>;
  showExternal() : Promise<void>;

}