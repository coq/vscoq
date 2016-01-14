/// <reference path="ui-util.ts" />
/// <reference path="StateModel.ts" />
'use strict';



function setText(text) {
  document.getElementById('stdout').innerHTML = text;
}

function message(text: string) {
}

function getQueryStringValue(key) {
    return decodeURI(window.location.search.replace(new RegExp("^(?:.*[&\\?]" + encodeURI(key).replace(/[\.\+\*]/g, "\\$&") + "(?:\\=([^&]*))?)?.*$", "i"), "$1"));
}

const stateModel = new StateModel();


function load() {
  var address = `ws://${getQueryStringValue('host')}:${getQueryStringValue('port')}`; 
  var connection = new WebSocket(address);
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
    inheritStyles(parent);
    message('OK'); 
  } catch(err) {
    message(err.toString()); 
  }  
}

