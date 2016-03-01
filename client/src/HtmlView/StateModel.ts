/// <reference path="ui-util.ts" />
'use strict';

enum HypothesisDifference { None, Changed, New, MovedUp, MovedDown }
enum TextDifference { None, Added, Removed }
interface TextPartDifference {
  text: string;
  change: TextDifference;
}
interface Hypothesis {
  identifier: string;
  relation: string;
  expression: string;
  diffExpression?: TextPartDifference[];
  diff: HypothesisDifference;
}
interface Goal {
  id: number;
  hypotheses: Hypothesis[];
  goal: string;
  diffGoal?: TextPartDifference[];
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

function getDifferenceClass(diff: HypothesisDifference) {
  switch(diff) {
    case HypothesisDifference.Changed:
      return ' changed';
    case HypothesisDifference.New:
      return ' new';
    case HypothesisDifference.MovedUp:
      return ' movedUp';
    case HypothesisDifference.MovedDown:
      return ' movedDown';
    default:
      return '';
  }
}

function createDiffText(parts: TextPartDifference[]) : Node[] {
  return parts.map((part) => {
    switch(part.change) {
      case TextDifference.Added:
        return makeElement('span',{class: 'charsAdded'},makeBreakingText(part.text))
      case TextDifference.Removed:
        return makeElement('span',{class: 'charsRemoved'},makeBreakingText(part.text))
      default:
        return makeElement('span',{},makeBreakingText(part.text));
    }
  })
}

function createHypothesis(hyp: Hypothesis) : Element {
  var hypE = makeElement('li', {class: 'hypothesis breakText' + getDifferenceClass(hyp.diff)},
    [ makeElement('span',{class:'ident'},makeText(hyp.identifier))
    , makeElement('span',{class:'rel'},makeText(hyp.relation))
    , makeElement('span',{class:'expr'},
      hyp.diffExpression
      ? createDiffText(hyp.diffExpression)
      : makeBreakingText(hyp.expression))
    ]);
  hypE.ondblclick = onDoubleClickBreakableText;
  return hypE;
}

function createHypotheses(hyps: Hypothesis[]) {
  return makeElement('ul',{class:"hypotheses"},
    hyps.map((hyp) => {
      return createHypothesis(hyp);
    }));
}

function createGoal(goal: Goal, idx:number, count:number) {
  return makeElement('li', {class:"goal"},
    [ makeElement('span',{class: 'goalId'},makeText(`${idx+1}/${count}`))
    , makeElement('span',{class: 'error'},[])
    , makeElement('span',{class: 'expr'},
      goal.diffGoal
      ? createDiffText(goal.diffGoal)
      : makeText(goal.goal))
    ]);
}

function createGoals(goals: Goal[]) {
  return makeElement('ul',{class:"goalsList"}, goals.map((g,i) => createGoal(g,i,goals.length)));
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

  private getFocusStatesE() {
    return this.statesE.getElementsByClassName(StateModel.focusedStateClass);
  }

  private getGoalsE() {
    return this.statesE.getElementsByClassName(StateModel.goalNodeClass);
  }

  private getCurrentGoalE() {
    return this.getGoalsE()[0];
  }

  private currentHypsE() {
    this.statesE.getElementsByClassName(StateModel.focusedStateClass).item(this.focusedState);
  }
  
  private setMessage(message: string) {
    // document.getElementById('messages').innerHTML = message;
    setChildren(document.getElementById('messages'), makeText(message));
  }

  private setErrorMessage(message: string) {
    const errorsN = this.getCurrentGoalE().getElementsByClassName('error');
    if(errorsN.length > 0)
    setChildren(errorsN.item(0), makeText(message));
    // document.getElementById('messages').innerHTML = message;
    // setChildren(document.getElementById('messages'), [makeElement('span',{class:'error'},[makeText(message)])]);
  }
  private clearErrorMessage() {
    const errorsN = this.getCurrentGoalE().getElementsByClassName('error');
    if(errorsN.length > 0)
      setChildren(errorsN.item(0), []);
  }
  
  public updateState(state: CoqTopGoalResult) {
    try {
      this.focusedState = 0;
      this.clearErrorMessage();
      // clearChildren(document.getElementById('messages'));
        
      if(state.error)
        this.setErrorMessage(state.error.message.toString());
      if (countAllGoals(state) == 0) {
        this.setMessage("No more subgoals.");
      } else if (state.goals) {
        if(state.goals.length > 0) {
          setChildren(this.statesE,
              state.goals.map((hp,idx) =>
                makeElement('div',{class: StateModel.focusedStateClass + (this.focusedState===idx ? "" : " hidden")},
                  [ createHypotheses(state.goals[idx].hypotheses)
                  , createGoal(state.goals[idx], idx, state.goals.length)
                  ])))
        } else
          this.setMessage("There are unfocused goals.");
      }
    } catch(err) {
      this.setMessage(err);
    }
  } 
}

