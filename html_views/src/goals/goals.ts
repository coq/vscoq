import * as stm from './StateModel'
import { ControllerEvent, ResizeEvent, SettingsState, ProofViewProtocol } from './protocol'

const stateModel = new stm.StateModel();


var throttleTimeout : number|null = null;
var throttleTimeoutCount = 0;
var throttleEventHandler = <X>(handler: (x:X) => void) => (event:X) => {
  throttleTimeoutCount = (throttleTimeoutCount + 1)%10;
  if(throttleTimeoutCount == 1)
    handler(event);
  else if(!throttleTimeout) {
    throttleTimeout = setTimeout(() => {
      throttleTimeout = null;
      handler(event);
    }, 500);
  }

    // handler(event);
  // throttleTimeout = setTimeout(() => {
  //   throttleTimeout = null;
  //   // handler(event);
  // }, 10);
}

function computePrintingWidth() {
  try {
    const stateView = $('#states')[0];
    const ctx = ($('#textMeasurer')[0] as HTMLCanvasElement).getContext("2d")!;
    ctx.font = getComputedStyle($('#textMeasurer')[0]).font || "";
    let widthChars = Math.floor(stateView.clientWidth / ctx.measureText("O").width);
    if (widthChars === Number.POSITIVE_INFINITY)
      widthChars = 1;
    widthChars = Math.max(widthChars,5);
    $('#measureTest').text("<" + "-".repeat(widthChars-2) + ">")
    if(vscode)
      vscode.postMessage(JSON.stringify(<ControllerEvent>{
        eventName: 'resize',
        params: <ResizeEvent>{columns: widthChars}
      }));
  } catch(error) {
    $('#stdout').text("!" + error);
  }
}

function onWindowGetFocus(event: FocusEvent) {
  try {
    if(vscode)
      vscode.postMessage(JSON.stringify(<ControllerEvent>{
        eventName: 'focus',
        params: {}
      }));
  } catch(error) {
  }
}

function setPrettifySymbolsMode(enabled: boolean) {
  $(document.body)
    .toggleClass("prettifySymbolsMode", enabled);
}

declare var acquireVsCodeApi : any;
const vscode = acquireVsCodeApi();

export function goalsLoad() {

  window.onresize = throttleEventHandler(event => computePrintingWidth);
  window.addEventListener("focus", onWindowGetFocus, true);

  window.addEventListener('message', event => {
    const message = event.data;
    handleMessage(message);
  });

  computePrintingWidth();
}


let currentCSSNode : HTMLLinkElement|null = null;
function loadCSS(filename: string) {
  // ref: http://stackoverflow.com/questions/9979415/dynamically-load-and-unload-stylesheets
  unloadCSS();
  var head = document.getElementsByTagName("head")[0];
  currentCSSNode = document.createElement('link');
  currentCSSNode.type = 'text/css';
  currentCSSNode.rel = 'stylesheet';
  currentCSSNode.media = 'screen';
  currentCSSNode.href = filename;
  head.appendChild(currentCSSNode);
}
function unloadCSS() {
  if(!currentCSSNode)
    return;
  var head = document.getElementsByTagName("head")[0];
  head.removeChild(currentCSSNode);
}

function updateSettings(settings: SettingsState) : void {
  if(settings.cssFile !== undefined)
    loadCSS(settings.cssFile);
  if(settings.prettifySymbolsMode !== undefined)
    setPrettifySymbolsMode(settings.prettifySymbolsMode);

  computePrintingWidth();
}

function handleMessage(message: ProofViewProtocol) : void {
  switch(message.command) {
    case 'goal-update':
      return stateModel.updateState(message.goal);
    case 'settings-update':
      updateSettings(message);
  }
}

addEventListener('load', goalsLoad);