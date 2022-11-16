import h = require("hyperscript");
import * as $ from "jquery";
import {
  ProofView,
  UnfocusedGoalStack,
  HypothesisDifference,
  TextDifference,
  AnnotatedText,
  ScopedText,
  Hypothesis,
  Goal,
  CommandResult,
} from "./protocol";
import { makeBreakingText } from "./ui-util";

function countUnfocusedGoals(u: UnfocusedGoalStack | undefined): number {
  if (!u) return 0;
  return u.before.length + u.after.length + countUnfocusedGoals(u.next);
}

function countAllGoals(state: ProofView): number {
  const result =
    (state.goals ? state.goals.length : 0) +
    countUnfocusedGoals(state.backgroundGoals) +
    (state.abandonedGoals ? state.abandonedGoals.length : 0) +
    (state.shelvedGoals ? state.shelvedGoals.length : 0);
  return result;
}

function getDifferenceClass(diff: HypothesisDifference) {
  switch (diff) {
    case HypothesisDifference.Changed:
      return " changed";
    case HypothesisDifference.New:
      return " new";
    case HypothesisDifference.MovedUp:
      return " movedUp";
    case HypothesisDifference.MovedDown:
      return " movedDown";
    default:
      return "";
  }
}

function getTextDiffClass(diff?: TextDifference): string {
  if (diff === "added") return "charsAdded";
  if (diff === "removed") return "charsRemoved";
  else return "";
}

function isScopedText(text: AnnotatedText): text is ScopedText {
  return text.hasOwnProperty("scope");
}

// TODO: setting a global variable like this could be a code smell
// I will find out a better way to write this
// let hasSubstitutions = false;

function createAnnotatedText(text: AnnotatedText): HTMLElement[] {
  function helper(text: AnnotatedText): (Text | HTMLElement)[] {
    if (typeof text === "string") return makeBreakingText(text);
    else if (text instanceof Array)
      return Array.prototype.concat(...text.map(helper));
    else if (isScopedText(text))
      return text.scope.trim() !== ""
        ? [
            $("<span>")
              .addClass(text.scope.replace(".", "-"))
              .append(helper(text.text))
              .get(0),
          ]
        : helper(text.text);
    else if (text.substitution) {
      // TextAnnotation
      // hasSubstitutions = true;
      return [
        $("<span>")
          .addClass("substitution")
          .addClass(getTextDiffClass(text.diff))
          .attr("subst", text.substitution)
          .attr("title", text.text)
          .append(makeBreakingText(text.text))
          .get(0),
      ];
    } // TextAnnotation
    else
      return [
        $("<span>")
          .addClass(getTextDiffClass(text.diff))
          .append(makeBreakingText(text.text))
          .get(0),
      ];
  }
  return [$("<span>").addClass("richpp").append(helper(text)).get(0)];
}

function onDoubleClickBreakableText(event: JQueryMouseEventObject) {
  // var target = <Element>event.currentTarget;
  if ($(event.currentTarget).hasClass("hypothesis")) {
    $(event.currentTarget).toggleClass("breakText");
    $(event.currentTarget).toggleClass("noBreakText");
  }
}

function createHypothesis(hyp: Hypothesis): JQuery {
  return $("<li>")
    .addClass("hypothesis")
    .addClass("breakText")
    .addClass(getDifferenceClass(hyp.diff))
    .append([
      $("<span>").addClass("ident").text(hyp.identifier),
      $("<span>").addClass("rel").text(hyp.relation),
      $("<span>")
        .addClass("expr")
        .append($(createAnnotatedText(hyp.expression))),
    ])
    .on("dblclick", onDoubleClickBreakableText);
}

function createHypotheses(hyps: Hypothesis[]) {
  return $("<ul>")
    .addClass("hypotheses")
    .append(hyps.map((hyp) => createHypothesis(hyp)));
}

function createGoal(goal: Goal, idx: number, count: number) {
  let expr = $("<span>").addClass("expr");
  expr.append($(createAnnotatedText(goal.goal)));
  if (idx == 0) {
    expr.attr("id", "firstGoal");
  }
  return $("<li>")
    .addClass("goal")
    .append([
      $("<span>")
        .addClass("goalId")
        .text(`${idx + 1}/${count}`),
      $("<span>").addClass("error"),
      expr,
    ]);
}

function createFocusedGoals(goals: Goal[]): JQuery {
  return $("<ul>")
    .addClass("goalsList")
    .append(goals.map((g, i) => createGoal(g, i, goals.length)));
}

export const ProofState = () => {
  const mainGoalsElement = h("vscode-panel-view");
  const shelvedGoalsElement = h("vscode-panel-view");
  const givenUpGoalsElement = h("vscode-panel-view");
  const element = h("vscode-panels.panels", [
    h("vscode-panel-tab", "MAIN"),
    h("vscode-panel-tab", "SHELVED"),
    h("vscode-panel-tab", "GIVEN UP"),
    mainGoalsElement,
    shelvedGoalsElement,
    givenUpGoalsElement,
  ]);

  const updateState = (state: ProofView) => {
    const handleNoMainGoals = (state: ProofView) => {
      if (countAllGoals(state) === 0) {
        mainGoalsElement.textContent = "Proof finished";
        return;
      }

      if (countUnfocusedGoals(state.backgroundGoals) > 0) {
        mainGoalsElement.textContent = "There are unfocused goals";
        return;
      }

      if (state.shelvedGoals.length > 0) {
        const content = h("span", [
          "There are shelved goals. Try using ",
          h("code", "Unshelve"),
        ]);
        mainGoalsElement.appendChild(content);
        return;
      }

      if (state.abandonedGoals.length > 0) {
        const content = h("span", [
          "There are some goals you gave up. You need to go back and solve them, or use ",
          h("code", "Admitted."),
        ]);
        mainGoalsElement.appendChild(content);
        return;
      }
    };

    mainGoalsElement.innerHTML = "";
    if (state.goals.length === 0) {
      handleNoMainGoals(state);
    } else {
      mainGoalsElement.appendChild(
        createHypotheses(state.goals[0].hypotheses)[0]
      );
      mainGoalsElement.appendChild(createFocusedGoals(state.goals)[0]);
    }
  };

  const unmount = () => {
    element.parentNode.removeChild(element);
  };

  return { element, updateState, unmount };
};

export const Infoview = () => {
  const element = h("div");

  let proofStateInstance : ReturnType<typeof ProofState> | undefined = undefined;

  const updateState = (state: CommandResult) => {
    if (state.type === "proof-view") {
      if (proofStateInstance === undefined) {
        element.innerHTML = "";
        proofStateInstance = ProofState();
        element.appendChild(proofStateInstance.element);
      }

      proofStateInstance.updateState(state);
    } else {
      if (proofStateInstance !== undefined) {
        proofStateInstance.unmount();
        proofStateInstance = undefined;
      }
    }

    // TODO: styling for these states
    if (state.type === "not-running") {
      element.textContent = "coqtop is not running";
    } else if (state.type === "failure") {
      element.appendChild(createAnnotatedText(state.message)[0]);
    } else if (state.type === "interrupted") {
      element.textContent = "Interrupted"
    } else if (state.type === "no-proof") {
      element.textContent = "Not in proof mode"
    }
  };

  const unmount = () => {
    element.parentNode.removeChild(element);
  };

  return { element, updateState, unmount };
};
