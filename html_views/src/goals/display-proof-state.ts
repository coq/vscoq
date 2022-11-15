import { CommandResult } from "./protocol";

export const ProofState = () => {
  const element = document.createElement("pre");

  const updateState = (state: CommandResult) => {
    element.textContent = JSON.stringify(state, undefined, 2);
    console.log(state);
  };

  return { element, updateState };
};
