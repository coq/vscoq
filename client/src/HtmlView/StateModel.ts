/// <reference path="ui-util.ts" />
'use strict';

interface Goal {
  id: number;
  hypotheses: string[];
  goal: string;
}

interface FailValue {
  message: string;
  location?: Location;
}

interface CoqTopGoalResult {
  goals?: Goal[];
  backgroundGoals?: Goal[],
  shelvedGoals?: Goal[],
  abandonedGoals?: Goal[],
  error?: FailValue;
}

enum DisplayState {
  Proof, Top, Error
}

function getDisplayState(state: CoqTopGoalResult) {
  if (state.error)
    return DisplayState.Error;
  if (state.goals || state.backgroundGoals || state.abandonedGoals || state.shelvedGoals)
    return DisplayState.Proof;
  else
    return DisplayState.Top;
}

function countAllGoals(state: CoqTopGoalResult): number {
  const result =
    (state.goals ? state.goals.length : 0)
    + (state.backgroundGoals ? state.backgroundGoals.length : 0)
    + (state.abandonedGoals ? state.abandonedGoals.length : 0)
    + (state.shelvedGoals ? state.shelvedGoals.length : 0);
  return result;
}

function createHypothesis(ident: string, rel: string, expr: string) : Element {
  return makeElement('li',{class: 'hypothesis'},
    [ makeElement('span',{class:'ident'},[makeText(ident)])
    , makeElement('span',{class:'rel'},[makeText(rel)])
    , makeElement('span',{class:'expr'},[makeText(expr)])
    ]);
}

function createHypotheses(hyps: string[]) {
  return makeElement('ul',{class:"hypotheses"},
    hyps.map((hyp) => {
      const split = hyp.split(/(:=|:)(.*)/);
      return createHypothesis(split[0],split[1],split[2]);
    }));
}

function createGoal(goal: string, idx:number, count:number) {
  return makeElement('li', {class:"goal"},
    [ makeElement('span',{class: 'id'},[makeText(`${idx}/${count}`)])
    , makeText(goal)
    ]);
}

function createGoals(goals: string[]) {
  return makeElement('ul',{}, goals.map((g,i) => createGoal(g,i,goals.length)));
}

class StateModel {
  private static hypothesesNodeClass = 'hypotheses';
  private static goalNodeClass = 'goal';
  private static focusedStateClass = 'focusedState';
  private statesE = document.getElementById('states');
  private focusedState = 0;
  private coqState : CoqTopGoalResult;
  
  constructor() {
  }
  
  private getCurrentStateE() {
    return this.statesE.getElementsByClassName(StateModel.focusedStateClass)[this.focusedState];
  }

  private getCurrentGoalE() {
    return this.getCurrentStateE().getElementsByClassName(StateModel.goalNodeClass)[0];
    
  }

  private currentHypsE() {
    this.statesE.getElementsByClassName(StateModel.focusedStateClass).item(this.focusedState);
  }
  
  private setMessage(message: string) {
    document.getElementById('messages').childNodes = createNodeList([makeText(message)]);
  }
  
  public updateState(state: CoqTopGoalResult) {
    try {
      this.focusedState = 0;
      clearChildren(this.statesE);
      if (countAllGoals(state) == 0) {
        this.setMessage("No more subgoals.");
      } else if (state.goals) {
        if(state.goals.length > 0) {
          setChildren(this.statesE,
              state.goals.map((hp,idx) =>
                makeElement('div',{class: StateModel.focusedStateClass + (this.focusedState===idx ? "" : " hidden")},
                  [ createHypotheses(state.goals[idx].hypotheses)
                  , createGoal(state.goals[idx].goal, idx, state.goals.length)
                  ])))
        } else
          this.setMessage("There are unfocused goals.");
      }
    } catch(err) {
      this.setMessage(err);
    }
  } 
}

