/// <reference path="../../typings/index.d.ts" />
/// <reference path="./ui-util.ts" />
/// <reference path="./StateModel.ts" />

interface ControllerEvent {
  eventName: string;
  params: ResizeEvent // | | | | | ;
}
interface ResizeEvent {
  columns: number;
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
    const ctx = (<HTMLCanvasElement>$('#textMeasurer')[0]).getContext("2d");
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
    $('#stdout').text("!" + error);    
  }
}

var connection : WebSocket = null;
function load() {
  window.onresize = throttleEventHandler(onWindowResize);

  if(parent.parent === parent)
    $(document.body).css({backgroundColor: 'black'});

  var address = `ws://${getQueryStringValue('host')}:${getQueryStringValue('port')}`; 
  connection = new WebSocket(address);
  connection.onopen = function (event) {
    $('#stdout').text("connected");
  }
  connection.onclose = function (event) {
    $('#stdout').text("connection closed");
  }
  connection.onerror = function (event) {
    $('#stdout').text("connection error");
  }
  connection.onmessage = function (event) {
    const state = <CoqTopGoalResult>JSON.parse(event.data);
    stateModel.updateState(state);
  }

}
