import * as $ from "jquery";
import { WebviewApi } from "vscode-webview";
import {
  ControllerEvent,
  ResizeEvent,
  SettingsState,
  ProofViewProtocol,
  ProofViewDiffSettings,
} from "./protocol";
import { Infoview } from "./display-proof-state";
import "@vscode/webview-ui-toolkit/dist/toolkit";
import h = require("hyperscript");

const infoview = Infoview();
const root = document.getElementById("root");
root.appendChild(infoview.element);

const throttleEventHandler = <X>(handler: (x: X) => void) => {
  let throttleTimeout: number | null = null;
  let throttleTimeoutCount = 0;

  return (event: X) => {
    throttleTimeoutCount = (throttleTimeoutCount + 1) % 10;
    if (throttleTimeoutCount == 1) handler(event);
    else if (!throttleTimeout) {
      throttleTimeout = window.setTimeout(() => {
        throttleTimeout = null;
        handler(event);
      }, 500);
    }
  };
};

// This function creates a DOM element that partially mimics the appearance
// of ProofState to calculate number of characters that can fit in a line.
//
// The element is briefly inserted into the DOM before getting removed.
// Users won't see it at all.
function computePrintingWidth() {
  const hypotheses = h(
    "ul.hypotheses",
    h("li", [h("span.ident", "a"), h("span.rel", "="), h("span.expr", "3")])
  );

  const pseudoview = h("vscode-panels.panels", [
    h("vscode-panel-tab", "MAIN"),
    h("vscode-panel-view", hypotheses),
  ]);

  document.body.appendChild(pseudoview);

  const clientWidth = hypotheses.clientWidth;
  const canvas = document.createElement("canvas");
  const context = canvas.getContext("2d");
  context.font = getComputedStyle(hypotheses).font || "monospace";
  const characterWidth = context.measureText("O").width;
  const characterCount = Math.max(Math.trunc(clientWidth / characterWidth), 1);
  vscode.postMessage(
    JSON.stringify(<ControllerEvent>{
      eventName: "resize",
      params: <ResizeEvent>{ columns: characterCount },
    })
  );

  document.body.removeChild(pseudoview);
}

function onWindowGetFocus(event: FocusEvent) {
  vscode.postMessage(
    JSON.stringify(<ControllerEvent>{
      eventName: "focus",
      params: {},
    })
  );
}

function setPrettifySymbolsMode(enabled: boolean) {
  $(document.body).toggleClass("prettifySymbolsMode", enabled);
}

function setProofViewDiffOptions(settings: ProofViewDiffSettings) {
  $(document.body).toggleClass(
    "proofView_addedTextIsItalic",
    settings.addedTextIsItalic
  );
  $(document.body).toggleClass(
    "proofView_removedTextIsStrikedthrough",
    settings.removedTextIsStrikedthrough
  );
}

declare const acquireVsCodeApi: any;
const vscode: WebviewApi<unknown> = acquireVsCodeApi();

function goalsLoad(_event: Event) {
  window.addEventListener(
    "resize",
    throttleEventHandler((event) => computePrintingWidth())
  );
  window.addEventListener("focus", onWindowGetFocus, true);

  let resizedOnFirstResponse = false;
  window.addEventListener("message", (event) => {
    if (!resizedOnFirstResponse) {
      resizedOnFirstResponse = true;
      computePrintingWidth();
    }
    const message = event.data;
    handleMessage(message);
  });

  computePrintingWidth();

  vscode.postMessage(
    JSON.stringify(<ControllerEvent>{
      eventName: "getGoal",
      params: {},
    })
  );
}

function updateSettings(settings: SettingsState): void {
  if (settings.prettifySymbolsMode !== undefined)
    setPrettifySymbolsMode(settings.prettifySymbolsMode);
  if (settings.proofViewDiff !== undefined)
    setProofViewDiffOptions(settings.proofViewDiff);
  computePrintingWidth();
}

function handleMessage(message: ProofViewProtocol): void {
  switch (message.command) {
    case "goal-update":
      return infoview.updateState(message.goal);
    case "settings-update":
      updateSettings(message);
  }
}

addEventListener("load", goalsLoad);
