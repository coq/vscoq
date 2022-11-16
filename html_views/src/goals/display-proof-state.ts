import { CommandResult } from "./protocol";
import { createFocusedGoals, createHypotheses } from "./StateModel";
import h = require("hyperscript");

export const ProofState = () => {
  // const element = document.createElement("pre");
  const mainGoalsElement = h("vscode-panel-view");
  const backgroundGoalsElement = h("vscode-panel-view", "background goals");
  const shelvedGoalsElement = h("vscode-panel-view", "shelved goals");
  const givenUpGoalsElement = h("vscode-panel-view", "given up goals");
  const element = h("vscode-panels.panels", [
    h("vscode-panel-tab", "MAIN"),
    h("vscode-panel-tab", "BACKGROUND"),
    h("vscode-panel-tab", "SHELVED"),
    h("vscode-panel-tab", "GIVEN UP"),
    mainGoalsElement,
    backgroundGoalsElement,
    shelvedGoalsElement,
    givenUpGoalsElement,
  ]);

  const updateState = (state: CommandResult) => {
    mainGoalsElement.innerHTML = "";
    if (state.type === "proof-view") {
      if (state.goals.length === 0) {
        mainGoalsElement.textContent = "No more goals (?)";
      } else {
        mainGoalsElement.appendChild(
          createHypotheses(state.goals[0].hypotheses)[0]
        );
        mainGoalsElement.appendChild(createFocusedGoals(state.goals)[0]);
      }
    } else if (state.type === "no-proof") {
      mainGoalsElement.textContent = "Not in proof mode.";
    }
  };

  return { element, updateState };
};
