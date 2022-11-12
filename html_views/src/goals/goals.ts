import * as $ from "jquery";
import { WebviewApi } from "vscode-webview";
import * as stm from "./StateModel";
import {
  ControllerEvent,
  ResizeEvent,
  SettingsState,
  ProofViewProtocol,
  ProofViewDiffSettings,
} from "./protocol";

const stateModel = new stm.StateModel();

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

function computePrintingWidth() {
  try {
    const stateView = $("#states")[0];
    const ctx = ($("#textMeasurer")[0] as HTMLCanvasElement).getContext("2d")!;
    ctx.font = getComputedStyle($("#textMeasurer")[0]).font || "";
    const widthClient = stateView.clientWidth - 27;
    const widthOneChar = ctx.measureText("O").width;
    let widthChars = Math.floor(widthClient / widthOneChar);
    if (
      widthClient <= 0 ||
      widthChars <= 1 ||
      widthChars === Number.POSITIVE_INFINITY
    ) {
      console.log(
        "Fallback to width 80 because: widthClient = " +
          widthClient +
          " and widthChars = " +
          widthChars
      );
      widthChars = 80;
    }
    $("#measureTest").text("<" + "-".repeat(widthChars - 2) + ">");
    vscode.postMessage(
      JSON.stringify(<ControllerEvent>{
        eventName: "resize",
        params: <ResizeEvent>{ columns: widthChars },
      })
    );
  } catch (error) {
    $("#stdout").text("!" + error);
  }
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
      return stateModel.updateState(message.goal);
    case "settings-update":
      updateSettings(message);
  }
}

addEventListener("load", goalsLoad);
