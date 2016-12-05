/// <reference path="../../typings/index.d.ts" />
/// <reference path="./ui-util.ts" />
/// <reference path="./StateModel.ts" />
/// <reference path="./protocol.ts" />

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

function computePrintingWidth() {
  try {
    const stateView = $('#states')[0];
    const ctx = ($('#textMeasurer')[0] as HTMLCanvasElement).getContext("2d");
    ctx.font = getComputedStyle($('#textMeasurer')[0]).font;
    let widthChars = Math.floor(stateView.clientWidth / ctx.measureText("O").width);
    if (widthChars === Number.POSITIVE_INFINITY)
      widthChars = 1;
    widthChars = Math.max(widthChars,5);
    $('#measureTest').text("<" + "-".repeat(widthChars-2) + ">")
    if(connection)
      connection.send(JSON.stringify(<ControllerEvent>{
        eventName: 'resize',
        params: <ResizeEvent>{columns: widthChars}
      }));  
  } catch(error) {
    $('#stdout').text("!" + error);    
  }
}

function onWindowGetFocus(event: FocusEvent) {
  try {
    if(connection)
      connection.send(JSON.stringify(<ControllerEvent>{
        eventName: 'focus',
        params: {}
      }));  
  } catch(error) {
  }
}

function getVSCodeTheme() : 'vscode-dark'|'vscode-light'|'vscode-high-contrast'|'' {
  switch($(parent.document.body).attr('class')) {
    case 'vscode-dark': return 'vscode-dark'
    case 'vscode-light': return 'vscode-light'
    case 'vscode-high-contrast': return 'vscode-high-contrast'
    default:
      return '';
  }
}

const observer = new MutationObserver(function(mutations) {
    inheritStyles(parent.parent);
    $(document.body).attr('class',getVSCodeTheme());
    // mutations.forEach(function(mutationRecord) {
    //   console.log(`{name: ${mutationRecord.attributeName}, old: ${mutationRecord.oldValue}, new: ${$(mutationRecord.target).attr('class')} }`);
    // });    
});

function togglePrettifySymbolsMode() {
  $(document.body)
    .toggleClass("prettifySymbolsMode");
}

var connection : WebSocket = null;
function load() {

  if(parent.parent === parent) {
    $(document.body).css({backgroundColor: 'black'});
  } else {
    try {
      window.onresize = throttleEventHandler(event => computePrintingWidth);
      window.addEventListener("focus", onWindowGetFocus, true);
      observer.observe(parent.document.body, { attributes : true, attributeFilter: ['class'] });
      inheritStyles(parent.parent);
      $(document.body)
        .removeClass("vscode-dark")
        .removeClass("vscode-light")
        .addClass(getVSCodeTheme());
    } catch(error) {
      $('#stdout').text(error.toString());    
      $('#error').text(error.toString());
      return;
    }
  }

  const address = `ws://${getQueryStringValue('host')}:${getQueryStringValue('port')}`; 
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
    const message = <ProofViewProtocol>JSON.parse(event.data);
    handleMessage(message);
  }

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
  if(settings.fontFamily)
    document.documentElement.style.setProperty(`--code-font-family`, settings.fontFamily);
  if(settings.fontSize)
    document.documentElement.style.setProperty(`--code-font-size`, settings.fontSize);
  if(settings.fontWeight)
    document.documentElement.style.setProperty(`--code-font-weight`, settings.fontWeight);
  if(settings.cssFile)
    loadCSS(settings.cssFile);

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