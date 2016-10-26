'use strict';
// import * as peg from 'pegjs'
import * as util from 'util'
import * as textUtil from './text-util'
import {Range, Position} from 'vscode-languageserver'
import * as server from './server'
import * as peg from 'pegjs'

const sentenceParser = peg.generate(`
SentenceLength
  = Sentence { throw text().length; } / "" {return error("Not a sentence")}

Sentence "sentence"
  = (_ (Bullet / (Command _ "." EndOfSentence)))

EndOfSentence
  = &Blank / !.

Command
  = (_ (LBr _ CommandP _ RBr / LBs _ CommandP _ RBs / String / CommandText))*
/* Once we're nested, commands may have periods */
CommandP
  = (_ (LBr _ CommandP _ RBr / LBs _ CommandP _ RBs / String / CommandTextP))*

CommandText
  = ([^()[\\]." \\t\\n\\r] / ("." !EndOfSentence))+
CommandTextP
  = [^()[\\]" \\t\\n\\r]+

String "string"
  = ["] ([^"] / "\\"\\"")* ["]

Bullet "bullet"
  = ( "*"+ / "+"+ / "-"+ / "{" / "}" )

_ "whitespace"
  = Blank* (Comment _)?

Blank "blank"
  = [ \\t\\n\\r]

LBr = [(] ![*]
RBr = [)]
LBs = [[]
RBs = [\\]]
LBc = "(*"
RBc = "*)"

Comment "comment"
  = LBc CommentText RBc

CommentText "commentText"
  = (String / Comment / ([^"*(] / ("(" !"*") / ("*" !")"))+ )*
`,{output: "parser"});

export function parseSentenceLength(str: string) : number {
  try {
    sentenceParser.parse(str, {startRule: "SentenceLength", tracer: undefined}) as string;
    return -1;
  } catch(error) {
    if(typeof error === 'number')
      return error;
    else
      return -1;
  }
}
























// const skipSentenceRE = /^(?:[^.("]|[.][^\s(]|[.][^\s]\([^*]|\([^*])*([.]|\(\*|")/;
// const skipSentenceRE = /^(?:[^.("]|[.][^\s]|\([^*])*([.]|\(\*|")/;

// sentence: ([^.]|[.][^\s])*[.]
// comment: ([^()]|\([^*])*(\(\*)
// string: ([^"])*"
// bullet: \s*[*]
// match up to 1) the first period (followed by but not including whitespace), 2) the start of a bracket ( or [, 3) the start of a comment or quote, 4) a bullet or 5) the end of the string.
// const skipSentenceOrBulletRE = /^(?:\s*)(?:([*\-+{}])|((?:[^.(["]|[.](?!\s))*)([.[(]|\(\*|"|$))/;
// const skipSentenceRE = /^(?:[^.(["]|[.](?!\s))*([.[(]|\(\*|"|$)/
// match up to the end of a quote
const skipStringRE = /^[^"]*("|$)/;
// match up to 1) the end of a comment or 2) the beginning of a (nested) comment
const skipCommentRE = /^(?:[^*(]|\*(?!\))|\((?!\*))*(\*\)|\(\*)|$/;

interface SentenceSkip {
  skip: number;
  terminator: string;
  bullet?: string;
  isPreWhitespace?: boolean;
}

function doSimpleSkip(str:string, idx:number, re: RegExp) : SentenceSkip {
  const match = re.exec(str.substr(idx));
  if(!match || match.length===0)
    throw 'anomaly: bad regex';
  // update our position to after the matched text
  return {
    skip: match[0].length,
    terminator: match[1]
  };
}

// function doSkipSentence(str:string, idx:number, allowBullet : boolean) : SentenceSkip {
//   if(allowBullet) {
//     const match = skipSentenceOrBulletRE.exec(str.substr(idx));
//     if(!match || match.length===0)
//       throw 'anomaly: bad regex';
//     // update our position to after the matched text
//     return {
//       skip: match[0].length,
//       bullet: match[1],
//       isPreWhitespace: match[2]===undefined || match[2].length === 0,
//       terminator: match[3]
//     };
//   } else
//     return doSimpleSkip(str,idx,skipSentenceRE);
// }

function doSkipComment(str:string, idx:number) : SentenceSkip {
  return doSimpleSkip(str,idx,skipCommentRE);
}

// function doSkipString(str:string, idx:number) : SentenceSkip {
//   return doSimpleSkip(str,idx,skipStringRE);
// }


/**
 * @returns the length of the parsed command or -1 if there is no [full] command
 * 
 * S::= BULLET  |  COMMENT S  |  P .
 * P::= ( P )  |  [ P ]  |  " P "  | TEXT P
 * COMMENT::= (* CSTUFF *) 
 * CSTUFF::= TEXT (* CSTUFF *) |
 * 
 */
// export function parseSentence(str: string) : number {
//   // Assume we are starting outside of a comment or parentheses
//   // match everything up to a period or beginning of a comment or string
//   let idx = 0;
//   let allowBullet = true; // whether a bullet may be expected (becomes false after the first non-whitespace)
  
//   while(true) {
//     const skipSen = doSkipSentence(str,idx,allowBullet);
//     idx+= skipSen.skip;

//     if(allowBullet && skipSen.bullet!=undefined)
//       break;
//     else if (allowBullet && !skipSen.isPreWhitespace)
//       allowBullet = false; // Some non-whitespace has appeared so we are no longer looking for bullets
//     else if(!allowBullet && skipSen.bullet!=undefined)
//       continue; // saw a bullet, but we are only looking for periods -- move on
    
      
//     if(skipSen.terminator === '.')
//       break; // we found the end of the sentence
//     else if (skipSen.terminator === '(') {
//     } else if (skipSen.terminator === '[') {
      
//     } else if(skipSen.terminator === '(*') {
//       // skip through [nested] comments
//       let nesting = 1;
//       while(nesting > 0) {
//         const skipCom = doSkipComment(str,idx);
//         idx+= skipCom.skip;
//         if(skipCom.terminator === '*)')
//           --nesting; // leaving a comment
//         else if(skipCom.terminator === '(*')
//           ++nesting; // need to recurse
//         else
//           throw "bad regex";
//       }
//     }
//     else if(skipSen.terminator === '"') {
//       // skip through string
//       idx+= doSkipString(str,idx).skip;
//     }
//     else if(skipSen.terminator === "") {
//       return -1; // end of string
//     }
//   }
//   return idx;
// }

// function isPassiveWhitespaceEdit(documentText: string, beginOffset: number, endOffset: number, changeText: string) : boolean {
//   const surroundingWS =
//     beginOffset === 0 || endOffset === documentText.length ||
//     /^\s$/.test(documentText.charAt(beginOffset - 1)) ||
//     /^\s$/.test(documentText.charAt(endOffset));
//   const changedText = documentText.substring(beginOffset, endOffset);

//   if (surroundingWS && /^\s*$/.test(changedText) && /^\s*$/.test(changedText))
//     return true; // whitespace --> whitespace
//   else if (/^\s+$/.test(changedText) && /^\s+$/.test(changedText))
//     return true; // whitespace --> whitespace
//   else
//     return false;  
// }

// /**
//  * Determines whether an edit should affect the validity of a sentence
//  * @param documentText: the Coq document or a sentence
//  * @param changeBegin: start offset of change w.r.t. `documentText`
//  * @param changeEnd: end offset of change w.r.t. `documentText`
//  * @param changeText: new text
//  * @returns `false` if the edit might change the validity of the sentence and thus needs to be reinterpreted
//  */
// function isPassiveEdit(documentText: string, beginOffset: number, endOffset: number, changeText: string) : boolean {
//   let idx = 0;
//   
//   
//   while(true) {
//     const skipSen = doSkipSentence(documentText, idx, false);
//     idx+= skipSen.skip;
// 
//     if(endOffset <= idx - skipSen.terminator.length || skipSen.terminator === '.') {
//       // the change is affecting a command
//       // only allow whitespace edits
//       return isPassiveWhitespaceEdit(documentText, beginOffset, endOffset, changeText);
//     } else if(endOffset <= idx)
//       return false; // edit affects a deliminator
//     else if(skipSen.terminator === '*')
//       continue;
//     else if(skipSen.terminator === '(*') {
//       let beginLevel = -1;
//       if(beginOffset < idx-skipSen.terminator.length)
//         beginLevel = 0; // start of edit is outside of comment
//       let nesting = 1;
//       while(nesting > 0) {
//         const skipCom = doSkipComment(str,idx);
//         idx+= skipCom.skip;
//         if(skipCom.terminator === '*)')
//           --nesting; // leaving a comment
//         else if(skipCom.terminator === '(*')
//           ++nesting; // need to recurse
//         else
//           throw "bad regex";
//       }
//     }
//     else if(skipSen.terminator === '"') {
//       // skip through string
//       idx+= doSkipString(str,idx).skip;
//     }
//     else if(skipSen.terminator === "") {
//       return -1; // end of string
//     }
//   }
//   return false;
// }

function removeComments(str: string) : string {
  // Assume we are starting outside of a comment or parentheses
  // match everything up to a period or beginning of a comment or string
  let result = ''; // accumulates normalized text
  let idx = 0;
  
  while(idx < str.length) {
     // find next comment deliminator
    const senMatch = /^((?:[^(]|\((?!\*))*)(\(\*)?/.exec(str.substring(idx));
    idx+= senMatch[0].length;
    result+= senMatch[1]; // accumulate everything but the comment
    
    if(senMatch[2] === '(*') {
      // skip through [nested] comments
      // do NOT accumulate result
      result+= ' ';
      let nesting = 1;
      while(nesting > 0) {
        const skipCom = doSkipComment(str,idx);
        idx+= skipCom.skip;
        if(skipCom.terminator === '*)')
          --nesting; // leaving a comment
        else if(skipCom.terminator === '(*')
          ++nesting; // need to recurse
        else
          throw "bad comment nesting";
      }
    }
  }
  return result;
}

function removeExcessWhitespace(str: string) : string {
  // Assume we are starting outside of a comment or parentheses
  // match everything up to a period or beginning of a comment or string
  let result = ''; // accumulates normalized text
  let idx = 0;
  
  while(idx < str.length) {
    const wsMatch = /^\s*/.exec(str.substring(idx));
    idx+= wsMatch[0].length;
    if(wsMatch[0].length > 0)
      result+= ' '; // keep one whitespace character

     // skip over non whitespace; but end at any beginning string deliminator
    const senMatch = /^((?:[^\s"])*)(")?/.exec(str.substring(idx));
    idx+= senMatch[0].length;
    result+= senMatch[1];
    
    if(senMatch[2] === '"') {
      result+= '"';
      // skip through string literal
      const matchStr = skipStringRE.exec(str.substring(idx));
      idx+= matchStr[0].length;
      result+= matchStr[0];
    }
  }
  return result;
}

export function normalizeText(str: string) : string {
  // Assume we are starting outside of a comment or parentheses
  return removeExcessWhitespace(removeComments(str));
}

// /**
//  * Determines whether an edit should affect the validity of a sentence
//  * @param documentText: the Coq document or a sentence
//  * @param changeBegin: start offset of change w.r.t. `documentText`
//  * @param changeEnd: end offset of change w.r.t. `documentText`
//  * @param changeText: new text
//  * @returns `false` if the edit might change the validity of the sentence and thus needs to be reinterpreted
//  */
// export function isPassiveEdit(documentText: string, beginOffset: number, endOffset: number, changeText: string) : boolean {
//   // Algorithm:
//   // 1. apply edit
//   // 2. normalize original & edited text
//   //   a) remove extra whitespace
//   //   b) remove comments
//   // 3. return true iff both normalized texts are still equal 
//   try {
//     const editedDocumentText = documentText.substring(0,beginOffset) + changeText + documentText.substring(endOffset);
//     return normalizeText(documentText) === normalizeText(editedDocumentText);
//   } catch(err) {
//     return false;
//   }
// }

/**
 * Determines whether the two commands are equivalent modulo whitespace and comments 
 * @returns `false` if the edit might change the validity of the sentence and thus needs to be reinterpreted
 */
export function isPassiveDifference(cmd1: string, cmd2: string) : boolean {
  try {
    // normalize: remove comments and collapse whitespace
    // special: it's okay for whitespace to be introduced or removed around closing period and at the beginning of a sentence 
    const normalized1 = normalizeText(' ' + cmd1.replace(/[.]\s*$/, ' . '));
    const normalized2 = normalizeText(' ' + cmd2.replace(/[.]\s*$/, ' . '));
    return normalized1 === normalized2;
  } catch(err) {
    return false;
  }
}


export enum SentenceRangeContainment {
  /** The range is contained by the sentence (range may be empty at the beginning, but not at the end and empty). Adjust sentence; check for invalidation */
  Contains,
  /** The range is before the sentence. Adjust sentence position */
  Before,
  /** The range is after the sentence. Ignore change. */
  After,
  /** The change crosses the sentence boundary. Invalidate sentence. */
  Crosses,
}
/** Determines whether a Coq sentence range should contain the range
 * A sentence contains a range if the range is nonempty and is completely within the sentence
 * OR if it is empty and at the *beginning* of a sentence.
 * (We only check the beginning because we assume sentences always end with a period (no more whitespace))
*/
export function sentenceRangeContainment(sentRange: Range, range: Range) : SentenceRangeContainment {
  if(textUtil.positionIsAfter(sentRange.start,range.end))
    return SentenceRangeContainment.Before; // change is strictly before sentence
  else if(textUtil.positionIsBeforeOrEqual(sentRange.end,range.start))
    return SentenceRangeContainment.After; // change is after sentence
  else if(textUtil.positionIsBeforeOrEqual(sentRange.start, range.start) && textUtil.positionIsAfterOrEqual(sentRange.end, range.end))
    return SentenceRangeContainment.Contains; // change is inside the sentence
  else if(textUtil.positionIsAfterOrEqual(sentRange.start,range.end))
    return SentenceRangeContainment.Before; // change is before sentence (maybe touching) and nonempty
  else
    return SentenceRangeContainment.Crosses;
    
}

