/// <reference path="./ui-util.ts" />
/// <reference path="./StateModel.ts" />
// import {StateModel, CoqTopGoalResult} from './StateModel'

interface ControllerEvent {
  eventName: string;
  params: ResizeEvent // | | | | | ;
}
interface ResizeEvent {
  columns: number;
}

function setText(text) {
  document.getElementById('stdout').innerHTML = text;
}

function message(text: string) {
}

function getQueryStringValue(key) {
    return decodeURI(window.location.search.replace(new RegExp("^(?:.*[&\\?]" + encodeURI(key).replace(/[\.\+\*]/g, "\\$&") + "(?:\\=([^&]*))?)?.*$", "i"), "$1"));
}

const stateModel = new StateModel();

var throttleTimeout = null;
var throttleTimeoutCount = 0;
var throttleEventHandler = <X>(handler: (X) => void) => (event:X) => {
  throttleTimeoutCount = (throttleTimeoutCount + 1)%10;
  if(throttleTimeoutCount == 1)
    handler(event);
  else if(!throttleTimeout) {
    clearTimeout(throttleTimeout);
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

function onWindowResize(event: UIEvent) {
  try {
    const stateView = document.body;
    const textMeasurer = <HTMLCanvasElement>document.getElementById('textMeasurer');
    const ctx = textMeasurer.getContext("2d");
    let widthChars = Math.floor(stateView.clientWidth / ctx.measureText("O").width);
    if (widthChars === Number.POSITIVE_INFINITY)
      widthChars = 1;
    // document.getElementById('stdout').innerHTML = ">" + widthChars;
    // document.getElementById('stdout').innerHTML = widthChars + '<br>' + new Array(Math.max(0,widthChars)+1).join('0');
    if(connection)
      connection.send(JSON.stringify(<ControllerEvent>{
        eventName: 'resize',
        params: <ResizeEvent>{columns: widthChars}
      }));  
  } catch(error) {
    document.getElementById('stdout').innerHTML = "!" + error;    
  }
}

var connection : WebSocket = null;
function load() {
  window.onresize = throttleEventHandler(onWindowResize);

  if(parent.parent === parent)
    document.body.style.backgroundColor = 'black';

  var address = `ws://${getQueryStringValue('host')}:${getQueryStringValue('port')}`; 
  connection = new WebSocket(address);
  connection.onopen = function (event) {
    document.getElementById('stdout').innerHTML = "connected";
  }
  connection.onclose = function (event) {
    document.getElementById('stdout').innerHTML = "connection closed";
  }
  connection.onerror = function (event) {
    document.getElementById('stdout').innerHTML = "connection error";
  }
  connection.onmessage = function (event) {
    const state = <CoqTopGoalResult>JSON.parse(event.data);
    stateModel.updateState(state);
  }
  
  try {
    //inheritStyles();
    // inheritStyles(parent);
    message('OK'); 
  } catch(err) {
    message(err.toString()); 
  }  
}
