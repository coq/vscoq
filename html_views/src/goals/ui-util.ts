
function importStyles(doc:Document) {
  var parentStyleSheets = doc.styleSheets as any as CSSStyleSheet[];
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


function inheritStyles(p:Window) {
 if (p) {
    importStyles(p.document);
    const pp = p.parent;
    if(pp !== p)
      inheritStyles(pp);
  }
}


function makeBreakingText(text: string) : Node[] {
  var txt = //makeElement('span',{class:'breakText',ondblclick: ''},
    // document.createTextNode(Array.prototype.map.call(text, (c) => /[\u00a0\u1680\u180e\u2000-\u200a\u2028\u2029\u202f\u205f\u3000\ufeff]/.test(c) ? ' ' : c).join(''));
    document.createTextNode(text.replace(/[\u00a0\u1680\u180e\u2000-\u200a\u2028\u2029\u202f\u205f\u3000\ufeff]/g, ' '))
    //);
  // txt.ondblclick = onDoubleClickBreakableText;
  return [txt];
}

