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

function makeBreakingText(text: string) : Node[] {
  var txt = //makeElement('span',{class:'breakText',ondblclick: ''},
    document.createTextNode(Array.prototype.map.call(text, (c) => /[\u00a0\u1680\u180e\u2000-\u200a\u2028\u2029\u202f\u205f\u3000\ufeff]/.test(c) ? ' ' : c).join(''))
    //);
  // txt.ondblclick = onDoubleClickBreakableText;
  return [txt];

  // return [makeElement('span',{class:'breakText'},
  //   text.split('\n').map((line,idx) => {
  //     if(idx === 0)
  //       return document.createTextNode(line)
  //     else {
  //       var it = /(\s*)(.*)/.exec(line);
  //       var indent = makeElement('span',{class:'hypLineIndent'},[document.createTextNode('\n' + Array(it[1].length).join(' '))]);
  //       // indent.innerHTML = '\n' + Array(it[1].length).join(' ');
  //       return makeElement('span',{class:'hypLine'},
  //         // [ makeElement('span',{class:'hypLineIndent'},[document.createTextNode('\n' + it[1]])
  //         [ indent
  //         , document.createTextNode(it[2])
  //         ]);
  //     }
  //   }))];

  // return [makeElement('span',{class:'breakText'}, [document.createTextNode(text)])];
  // return  text.split('\n').map((line,idx) => {
  //     if(idx === 0)
  //       return document.createTextNode(line)
  //     else {
  //       var it = /(\s*)(.*)/.exec(line);
  //       return makeElement('span',{class:'hypLine'},
  //         [ makeElement('span',{class:'hypLineIndent'},[document.createTextNode(it[1])])
  //         , makeElement('span',{class:'hypLineText'},[document.createTextNode(it[2])])
  //         ]);
  //     }
  //   });
  //   
  // return text.split('\n').map((t, idx) =>
  //   idx === 0
  //   ? document.createTextNode(text)
  //   : makeElement('span',{class:'hypLine'},[document.createTextNode(t)])
  // );
}

function makeText(text: string) : Node[] {
  return [document.createTextNode(text)];
}

function hideElement(e: Element) {
  if(e)
    e.className = 'hidden ' + e.className;
}

function toggleHideElement(e: Element) {
  if(e && e.className.indexOf('hidden') == -1)
    hideElement(e);
  else
    showElement(e);
}

function showElement(e: Element) {
  if(e)
    e.className = e.className.replace(/\bhidden\b/,'');
}

function clearChildren(e: Element) {
  if(e) while(e.firstChild)
    e.removeChild(e.firstChild)
}
