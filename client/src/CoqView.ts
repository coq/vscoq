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

export function countAllGoals(state: proto.CoqTopGoalResult): number {
  const result =
    (state.goals ? state.goals.length : 0)
    + (state.backgroundGoals ? state.backgroundGoals.length : 0)
    + (state.abandonedGoals ? state.abandonedGoals.length : 0)
    + (state.shelvedGoals ? state.shelvedGoals.length : 0);
  return result;
}

export interface CoqView extends vscode.Disposable {

  update(state: proto.CoqTopGoalResult) : void;
  // message(message: string) : void;
  onresize: (columns: number) => Thenable<void>;

}