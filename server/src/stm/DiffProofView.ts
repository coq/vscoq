// 'use strict';

import * as coqProto from '../coqtop/coq-proto';
import {ProofView, Goal, Hypothesis, AnnotatedText, HypothesisDifference, TextAnnotation, ScopedText} from '../protocol';
import * as text from '../util/AnnotatedText';
import * as server from '../server';



function diffHypotheses(oldHyps: Hypothesis[], newHyps: Hypothesis[]) {
  newHyps.forEach((hyp,idxHyp) => {
    var oldHypIdx = idxHyp;
    var oldHyp = oldHyps[oldHypIdx];
    if(oldHyp === undefined || oldHyp.identifier !== hyp.identifier) {
      oldHypIdx = oldHyps.findIndex((h) => h.identifier === hyp.identifier)
      oldHyp = oldHyps[oldHypIdx];
    }

    if(oldHyp === undefined)
      hyp.diff = HypothesisDifference.New;
    else {
      const diff = text.diffText(oldHyp.expression,hyp.expression);
      hyp.expression = diff.text;
      hyp.diff = diff.different ? HypothesisDifference.Changed : HypothesisDifference.None
    }
  })
}

function diffGoals(oldGoals: Goal[], newGoals: Goal[]) {
  if(!newGoals || !oldGoals)
    return;
  newGoals.forEach((g,idxGoal) => {
    if(oldGoals[idxGoal] !== undefined) {
      diffHypotheses(oldGoals[idxGoal].hypotheses, g.hypotheses);
      g.goal = text.diffText(oldGoals[idxGoal].goal,g.goal).text;
    }
  })

}

export function diffProofView(oldState: ProofView, newState: ProofView) {
  try {
    diffGoals(oldState.goals, newState.goals);
  } catch(err) {
    server.connection.console.error('diffGoals threw an exception: ' + err.toString());
  }
}

