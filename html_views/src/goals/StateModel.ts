/// <reference path="../../typings/index.d.ts" />
/// <reference path="ui-util.ts" />


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
  goal: string|{string:string};
  diffGoal?: TextPartDifference[];
}
interface UnfocusedGoalStack {
  // subgoals that appear before the focus
  before: Goal[];
  // reference to the more-focused background goals
  next?: UnfocusedGoalStack
  // subgoals that appear after the focus
  after: Goal[];
}

interface FailValue {
  message: string;
  location?: Location;
}

interface ProofView {
  goals: Goal[];
  backgroundGoals: UnfocusedGoalStack,
  shelvedGoals: Goal[],
  abandonedGoals: Goal[],
}

interface CommandInterrupted {
  range: any
}

type FocusPosition = {focus: any}
type NotRunningTag = {type: 'not-running'}
type NoProofTag = {type: 'no-proof'}
type FailureTag = {type: 'failure'}
type ProofViewTag = {type: 'proof-view'}
type InterruptedTag = {type: 'interrupted'}
type NotRunningResult = NotRunningTag
type NoProofResult = NoProofTag
type FailureResult = FailValue & FailureTag
type ProofViewResult = ProofView & ProofViewTag
type InterruptedResult = CommandInterrupted & InterruptedTag
type CommandResult =
  NotRunningTag |
  (FailureResult & FocusPosition) |
  (ProofViewResult & FocusPosition) |
  (InterruptedResult & FocusPosition) |
  (NoProofResult & FocusPosition);


enum DisplayState {
  Proof, Top, Error, NotRunning, NoProof, Interrupted
}

function getDisplayState(state: CommandResult) {
  switch(state.type) {
    case 'failure':
      return DisplayState.Error;
    case 'proof-view':
      return DisplayState.Proof;
    case 'not-running':
      return DisplayState.NotRunning;
    case 'no-proof':
      return DisplayState.NoProof;
    case 'interrupted':
      return DisplayState.Interrupted;
  }
}

function countUnfocusedGoals(u: UnfocusedGoalStack) {
  if(!u)
    return 0;
  return u.before.length + u.after.length + countUnfocusedGoals(u.next);
}

function countAllGoals(state: ProofView): number {
  const result =
    (state.goals ? state.goals.length : 0)
    + countUnfocusedGoals(state.backgroundGoals)
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

function getTextDiffClass(diff: TextDifference) : string {
  switch(diff) {
    case TextDifference.Added: return 'charsAdded'
    case TextDifference.Removed: return 'charsRemoved'
    default: return ''
  }
}

function createDiffText(parts: TextPartDifference[]) : Node[] {
  return parts.map((part) =>
    $('<span>')
    .addClass(getTextDiffClass(part.change))
    .append(makeBreakingText(part.text))
    [0]
    );
}

function onDoubleClickBreakableText(event: JQueryMouseEventObject) {
  var target = <Element>event.currentTarget;
  if($(event.currentTarget).hasClass('hypothesis')) {
    $(event.currentTarget).toggleClass('breakText');
    $(event.currentTarget).toggleClass('noBreakText');
  }
}

function createHypothesis(hyp: Hypothesis) : JQuery {
  return $('<li>')
    .addClass('hypothesis')
    .addClass('breakText')
    .addClass(getDifferenceClass(hyp.diff))
    .append(
      [ $('<span>').addClass('ident').text(hyp.identifier)
      , $('<span>').addClass('rel').text(hyp.relation)
      , $('<span>').addClass('expr')
        .append(hyp.diffExpression
            ? $(createDiffText(hyp.diffExpression))
            : $(makeBreakingText(hyp.expression)))
      ])
    .on('dblclick', onDoubleClickBreakableText)

}

function createHypotheses(hyps: Hypothesis[]) {
  return $('<ul>')
    .addClass('hypotheses')
    .append(hyps.map((hyp) => createHypothesis(hyp)));
}

function createGoal(goal: Goal, idx:number, count:number) {
  let expr = $('<span>').addClass('expr');
  if(goal.diffGoal)
    expr.append(createDiffText(goal.diffGoal))
  else if(typeof goal.goal === 'string')
    expr.text(goal.goal)
  else
    expr.text((<{string:string}>goal.goal).string)
  return $('<li>')
    .addClass('goal')
    .append(
      [ $('<span>').addClass('goalId').text(`${idx+1}/${count}`)
      , $('<span>').addClass('error')
      , expr
      ]);
}

function createGoals(goals: Goal[]) {
  return $('<ul>')
    .addClass('goalsLists')
    .append(goals.map((g,i) => createGoal(g,i,goals.length)));
}

function createFocusedGoals(goals: Goal[]) : JQuery {
  return $('<ul>')
    .addClass('goalsList')
    .append(goals.map((g,i) => createGoal(g,i,goals.length)));
  // return $(goals.map((g,idx) =>
  //   createGoal(g, idx, goals.length)));
}





class StateModel {
  private static hypothesesNodeClass = '.hypotheses';
  private static goalNodeClass = '.goal';
  private static focusedStateClass = '.focusedState';
  private focusedState = 0;
  private coqState : ProofView;

  constructor() {
  }


  private setMessage(message: string) {
    $('#messages').text(message);
  }

  private setErrorMessage(message: string) {
    $('#error').text(message);
  }
  private clearErrorMessage() {
    $('#error').empty();
  }

  public updateState(state: CommandResult) {
    try {
      this.focusedState = 0;
      this.clearErrorMessage();
      $('#stdout').text('');

      if(state.type === 'failure')
        this.setErrorMessage(state.message.toString());
      else if(state.type === 'not-running') 
        this.setMessage('Not running.');
      else if(state.type === 'no-proof')
        this.setMessage('Not in proof mode.');
      else if(state.type === 'interrupted')
        this.setMessage("Interrupted.");
      else if(state.type === 'proof-view') { 
        if (countAllGoals(state) == 0) {
          $('#states').empty();
          this.setMessage("No more subgoals.");
        } else if (state.goals) {
          if(state.goals.length > 0) {
            this.setMessage("");
            $('#states')
            .empty()
            .append(
              [ createHypotheses(state.goals[0].hypotheses)
              , createFocusedGoals(state.goals)
            ])
          } else {
            $('#states').empty();
            this.setMessage("There are unfocused goals.");
          }
        }
    }
      //   case 'not-running':
      //     return DisplayState.NotRunning;
      //   case 'no-proof':
      //     return DisplayState.NoProof;
      //   case 'interrupted':
      //     return DisplayState.Interrupted;
      // }

    } catch(err) {
      this.setMessage(err);
    }
  }
}
