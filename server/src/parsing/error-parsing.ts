/*
Errors:
  "@{ident} already exists"
  "@{ident} cannot be defined."
  "@{ident} is already used"
  "@{ident} is not a local definition"
  "@{ident} is used in conclusion"
  "@{ident} is used in hypothesis @{ident'}"
  "@{ident} is used in the conclusion"
  "@{ident} is used in the hypothesis @{ident'}"
  "@{qualid} is not a module"
  "Argument of match does not evaluate to a term"
  "arguments of ring_simplify do not have all the same type"
  "Attempt to save an incomplete proof"
  "bad lemma for decidability of equality"
  "Bad magic number"
  "bad ring structure"
  "cannot be used as a hint"
  "Cannot build functional inversion principle"
  "Cannot define graph for @{ident}@{hole}"
  "Cannot define principle(s) for @{ident}@{hole}"
  "cannot find a declared ring structure for equality term"
  "cannot find a declared ring structure over term"
  "Cannot find induction information on @{qualid}"
  "Cannot find inversion information for hypothesis @{ident}"
  "Cannot find library foo in loadpath"
  "Cannot find the source class of @{qualid}"
  "Cannot handle mutually (co)inductive records."
  "Cannot infer a term for this placeholder"
  "Cannot load @{qualid}: no physical path bound to @{dirpath}"
  "Cannot move @{ident} after @{ident}: it depends on @{ident}"
  "Cannot move @{ident} after @{ident}: it occurs in @{ident}"
  "Cannot recognize @{class} as a source class of @{qualid}"
  "Cannot solve the goal"
  "Cannot use mutual definition with well-founded recursion or measure"
  "Can’t find file @{ident} on loadpath"
  "Compiled library @{ident}.vo makes inconsistent assumptions over library @{qualid}"
  "Condition not satisfied"
  "does not denote an evaluable constant"
  "does not respect the uniform inheritance condition"
  "Failed to progress"
  "File not found on loadpath : \"@{string}\""
  "Found target class @{class} instead of @{class}"
  "Funclass cannot be a source class"
  "goal does not satisfy the expected preconditions"
  "Goal is solvable by congruence but some arguments are missing. Try \"congruence with @{hole}\", replacing metavariables by arbitrary terms."
  "Hypothesis @{ident} must contain at least one Function"
  "I don’t know how to handle dependent equality"
  "Impossible to unify @{hole} with @{hole}"
  "In environment @{hole} the term: @{term} does not have type @{term}"
  "invalid argument"
  "Invalid backtrack"
  "is already a coercion"
  "is not a function"
  "is not an inductive type"
  "Loading of ML object file forbidden in a native Coq"
  "Module/section @{module} not found"
  "must be a transparent constant"
  "name @{ident} is already used"
  "No applicable tactic"
  "No argument name @{ident}"
  "No discriminable equalities"
  "No evars"
  "No focused proof"
  "No focused proof (No proof-editing in progress)"
  "No focused proof to restart"
  "No matching clauses for match"
  "No matching clauses for match goal"
  "No primitive equality found"
  "No product even after head-reduction"
  "No progress made"
  "No such assumption"
  "No such binder"
  "no such entry"
  "No such goal"
  "No such goal. Focus next goal with bullet @{bullet}."
  "No such goal. Try unfocusing with \"}\"."
  "No such hypothesis"
  "No such hypothesis in current goal"
  "No such label @{ident}"
  "Non exhaustive pattern-matching"
  "Non strictly positive occurrence of @{ident} in @{type}"
  "not a context variable"
  "not a defined object"
  "Not a discriminable equality"
  "Not a primitive equality"
  "Not a projectable equality but a discriminable one"
  "Not a proposition or a type"
  "not a valid ring equation"
  "Not a variable or hypothesis"
  "Not an evar"
  "Not an exact proof"
  "Not an inductive goal with 1 constructor"
  "Not an inductive goal with 2 constructors"
  "Not an inductive product"
  "Not convertible"
  "not declared"
  "Not enough constructors"
  "Not equal"
  "Not reducible"
  "Not the right number of induction arguments"
  "Not the right number of missing arguments"
  "Not unifiable"
  "Nothing to do, it is an equality between convertible terms"
  "Nothing to rewrite"
  "omega can’t solve this system"
  "omega: Can’t solve a goal with equality on @{type}"
  "omega: Can’t solve a goal with non-linear products"
  "omega: Can’t solve a goal with proposition variables"
  "omega: Not a quantifier-free goal"
  "omega: Unrecognized atomic proposition: @{prop}"
  "omega: Unrecognized predicate or connective: @{ident}"
  "omega: Unrecognized proposition"
  "Proof is not complete"
  "quote: not a simple fixpoint"
  "Records declared with the keyword Record or Structure cannot be recursive."
  "Require is not allowed inside a module or a module type"
  "ring @{operation} should be declared as a morphism"
  "Signature components for label @{ident} do not match"
  "Sortclass cannot be a source class"
  "Statement without assumptions"
  "Tactic Failure @{message} (level @{n})"
  "Tactic generated a subgoal identical to the original goal"
  "terms do not have convertible types"
  "The @{num}th argument of @{ident} must be @{ident'} in @{type}"
  "The conclusion is not a substitutive equation"
  "The conclusion of @{type} is not valid; it must be built from @{ident}"
  "The file @{ident}.vo contains library @{dirpath} and not library @{dirpath'}"
  "The recursive argument must be specified"
  "The reference @{qualid} was not found in the current environment"
  "The term @{form} has type @{hole} which should be Set, Prop or Type"
  "The term @{term} has type @{type} while it is expected to have type @{type}"
  "The term provided does not end with an equation"
  "The variable @{ident} is already defined"
  "This is not the last opened module"
  "This is not the last opened module type"
  "This is not the last opened section"
  "This proof is focused, but cannot be unfocused this way"
  "This tactic has more than one success"
  "Unable to apply"
  "Unable to find an instance for the variables @{ident+}"
  "Unable to satisfy the rewriting constraints"
  "Undeclared universe @{ident}"
  "Universe inconsistency"
  "Variable @{ident} is already declared"
  "Wrong bullet @{bullet}1 : Bullet @{bullet}2 is mandatory here."
  "Wrong bullet @{bullet}1 : Current bullet @{bullet}2 is not finished."

Diff:
  "Found target class @{class} instead of @{class}"
  "Impossible to unify @{hole} with @{hole}"
  "The file @{ident}.vo contains library @{dirpath} and not library @{dirpath'}"
  "The term @{term} has type @{type} while it is expected to have type @{type}"

*/

import * as diff from 'diff'

import {AnnotatedText} from '../util/AnnotatedText'
import * as text from '../util/AnnotatedText'

/** Error messages that compare two terms that should be equal */
const diffMessages = [
  {pre: /^\s*(?:Error:\s+)?(?:.*\n)*Found\s+target\s+class\s+"/, mid: /"\s+instead\s+of\s+"/g, post: /"[.]?$/},
  {pre: /^\s*(?:Error:\s+)?(?:.*\n)*Impossible\s+to\s+unify\s+"/, mid: /"\s+with\s+"/g, post: /"[.]?$/},
  {pre: /^\s*(?:Error:\s+)?(?:.*\n)*Unable\s+to\s+unify\s+"/, mid: /"\s+with\s+"/g, post: /"[.]?$/},
  {pre: /^\s*(?:Error:\s+)?(?:.*\n)*Refiner\s+was\s+given\s+an\s+argument\s+".*?"\s+of\s+type\s+"/, mid: /"\s+instead\s+of\s+"/g, post: /"[.]?$/},
  {pre: /^\s*(?:Error:\s+)?(?:.*\n)*The\s+file\s+.*?\.vo\s+contains\s+library\s+/, mid: /\s+and\s+not\s+library\s+/, post: /[.]?$/},
  {pre: /^\s*(?:Error:\s+)?(?:.*\n)*The\s+term\s+.*?\s+has\s+type\s+"/, mid: /"\s+while\s+it\s+is\s+expected\s+to\s+have\s+type\s+"/, post: /"[.]?$/},
];

function* indicesOf(str: string, substr: string|RegExp, start?: number, end?: number) : Iterable<[number,number]> {
  function indexOf(str: string,substr: string|RegExp, pos: number) : [number,number] {
    if(typeof substr==='string') {
      const i = str.indexOf(substr,pos);
      return [i, i >=0 ? i+substr.length : 0]
    } else {
      substr.lastIndex = pos;
      const m = substr.exec(str);
      if(!m || m.index < pos)
        return [-1,0];
      else
        return [m.index, m.index+m[0].length];
    }
  }
  start = start || 0;
  end = end || start;
  let pos = start;

  let idx = indexOf(str,substr,pos);
  while(idx[0] >= 0 && pos < end) {
    yield idx;
    pos = idx[0]+1;
    idx = indexOf(str,substr,pos);
  }
}

function costOfDifference(d: diff.Change[]): number {
  return d.reduce((v,x) => v + (x.added||x.removed ? x.value.length : 0), 0);
}

export function parseError(txt: AnnotatedText) : AnnotatedText {
  const str = text.textToDisplayString(txt);
  df: for(let df of diffMessages) {
    const preMatch = df.pre.exec(str);
    const postMatch = preMatch ? df.post.exec(str) : undefined;
    if(preMatch && postMatch) {
      const preLen = preMatch[0].length;
      const postLen = postMatch[0].length;
      const diffMatches: {
        x: string;
        y: string;
        mid: [number, number];
        diff: diff.Change[];
        cost: number;
      }[] = [];
      for (let mid of indicesOf(str, df.mid, preLen, str.length - postLen)) {
        const x = str.substring(preLen, mid[0]);
        const y = str.substring(mid[1], str.length - postLen);
        const xy = diff.diffWords(x, y);
        diffMatches.push({
          x: x,
          y: y,
          mid: mid,
          diff: xy,
          cost: costOfDifference(xy)
        });
      }
      if(diffMatches.length === 0)
        continue df;
      const match = diffMatches.sort((a,b) => a.cost < b.cost ? -1 : a.cost === b.cost ? 0 : 1)[0];

      const pre = text.subtextCount(txt, 0, preLen);
      const part1 = text.subtextCount(txt, preLen, match.x.length);
      const mid = text.subtext(txt, match.mid[0], match.mid[1]);
      const part2 = text.subtextCount(txt, match.mid[1], match.y.length);
      const post = text.subtextCount(txt, match.mid[1]+match.y.length, postLen);
      const part1Delta = text.annotateDiffAdded(part1,match.diff,{diffSubstitutions: true, mode: "old"});
      const part2Delta = text.annotateDiffAdded(part2,match.diff,{diffSubstitutions: true, mode: "new"});
      return text.normalizeText(text.append(pre,part1Delta,mid,part2Delta,post));
    }
  }
  return txt;
}
