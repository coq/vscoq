/// <reference path="refs.d.ts" />
'use strict';

function importStyles(doc) {
  var parentStyleSheets = <CSSStyleSheet[]>doc.styleSheets;
  var cssString = "";
  for (var i = 0, count = parentStyleSheets.length; i < count; ++i) {
    if (parentStyleSheets[i].cssRules) {
      var cssRules = parentStyleSheets[i].cssRules;
      for (var j = 0, countJ = cssRules.length; j < countJ; ++j)
        cssString += cssRules[j].cssText;
    }
    else
      cssString += parentStyleSheets[i].cssText;  // IE8 and earlier
  }
  var style = document.createElement("style");
  style.type = "text/css";
  style.innerHTML = cssString;
  // message(cssString);
  document.getElementsByTagName("head")[0].appendChild(style);
}

// function inheritStyles() {
//   if (parent) {
//       var oHead = document.getElementsByTagName("head")[0];
//       var arrStyleSheets = parent.document.getElementsByTagName("style");
//       for (var i = 0; i < arrStyleSheets.length; i++)
//           oHead.appendChild(arrStyleSheets[i].cloneNode(true));
//   } 
// }

function inheritStyles(p) {
  if (p) {
    importStyles(p.document);
    const pp = p.parent;
    if(pp !== p)
      inheritStyles(pp);
  }
}

function setAttributes<T extends Element>(obj: T, attrs: any) : T {
  for(const attr in attrs)
    if(attrs.hasOwnProperty(attr))
      obj.setAttribute(attr, attrs[attr]);
  return obj;
}

function createNodeList(nodes: Node[]) : NodeList {
  var resultN = document.createDocumentFragment();
  nodes.forEach((n) => resultN.appendChild(n));
  return resultN.childNodes;
}

function setChildren<T extends Element>(obj: T, children: Node[]) : T {
    clearChildren(obj);
    for(const child of children)
      obj.appendChild(child);
    return obj;
}


function makeElement(tag: string, attrs?: any, children?: Node[]) {
  const resultN = document.createElement(tag);
  setAttributes(resultN,attrs)
  setChildren(resultN,children);
  return resultN;
}

function makeText(text: string) : Node {
  return document.createTextNode(text);
}

function hideElement(e: Element) {
  if(e)
    e.className = 'hidden ' + e.className;
}

function showElement(e: Element) {
  if(e)
    e.className = e.className.replace(/\bhidden\b/,'');
}

function clearChildren(e: Element) {
  if(e) while(e.firstChild)
    e.removeChild(e.firstChild)
}
