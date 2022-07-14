'use strict';
import * as vscode from 'vscode';
import { CoqProject } from './CoqProject';
import * as editorAssist from './EditorAssist';

function operator_regex(str: string) {
  // Matching operators is simple, as Coq will kindly
  // print spaces before and after them,
  // we use lookahead/lookbehind to avoid catching them
  return new RegExp("(?<=\\s)" + str + "(?=\\s)", "g");
}

function formatHover(response: string) {
  // response is the string printed by "Check a." :
  // |a
  // |\t : Type
  // |       type (continued if long) (7 space indent)
  // |where
  // |?optional = whatever

  // § Strip output of anything but the type
  const array = response.split("\nwhere\n");
  let type = array[0];
  // let where = array[1];
  type = type.replace(/^.*?\n\t : /, ""); // remove identifier
  type = type.replace(/^ {7}/gm, ""); // remove indent

  // § Format the type to be pretty and compact (e.g. replace forall with ∀)
  const replaces = [
    { match: /\bfun\b/g, subst: "λ" },
    { match: /\bforall\b/g, subst: "∀" },
    { match: /\bexists\b/g, subst: "∃" },
    { match: operator_regex("\\\\\\/"), subst: "∨" },
    { match: operator_regex("\\/\\\\"), subst: "∧" },
    { match: operator_regex("<->"), subst: "⟷" }, // the default arrow "↔" is too small/low...
    { match: operator_regex("->"), subst: "➞" }, // the default arrow "→" is too small/low...
    { match: operator_regex("<="), subst: "≤" },
    { match: operator_regex(">="), subst: "≥" },
    // {match:operator_regex("=>"), subst:"⇒"}, // very ugly render
    { match: operator_regex("<>"), subst: "≠" },
    { match: operator_regex("~"), subst: "¬" }
  ];
  for (const replace of replaces) {
    type = type.replace(replace.match, replace.subst);
  }

  if (type === "") return;

  let hover = [{ language: "coq", value: type }];
  // if (where)
  //  hover.push({language:"coq", value:where});
  return new vscode.Hover(hover);
}

// Perform a query to get hover text
async function queryHover(text: string, project: CoqProject, document: vscode.TextDocument) {
  const doc = project.getOrCurrent(document.uri.toString());
  if (!doc) return;
  const response = await doc.hoverQuery(text);
  return response;
}

// VSCode calls HoverProvider repeatedly
// So we memoize recent results to avoid having to requery
type query_result = { input: string, time: number, output: vscode.Hover };

let recent_queries: query_result[] = [];
const query_redo_delay = 5000; // milliseconds

function filterOld(query: query_result) {
  return Date.now() - query.time >= query_redo_delay;
}

export const regExpCoqNotation = /[^\p{Z}\p{C}"]+/u;

export function coqIdOrNotationFromRange(document: vscode.TextDocument, range: vscode.Range | undefined) {
  let text = document.getText(range);
  if (new RegExp("\^" + regExpCoqNotation.source + "\$", regExpCoqNotation.flags).test(text)
    && !new RegExp("\^" + editorAssist.regExpQualifiedCoqIdent.source + "\$", regExpCoqNotation.flags).test(text))
    return "\"" + text + "\"";
  return text;
}

export async function provideHover(position: vscode.Position, project: CoqProject, document: vscode.TextDocument) {
  // § Get text under cursor
  let range = document.getWordRangeAtPosition(position);
  if (!range)
    range = document.getWordRangeAtPosition(position, regExpCoqNotation);
  const input = coqIdOrNotationFromRange(document, range).trim();
  if (input === "") return;

  // § Check if query was recently performed
  recent_queries = recent_queries.filter(filterOld);
  const has_query = recent_queries.filter((query) => query.input === input)[0];
  if (has_query)
    return has_query.output;

  // § if not, perform query
  const response = await queryHover(input, project, document);
  if (!response) return;
  const output = formatHover(response);
  if (!output) return;

  // § Add query to recent queries
  recent_queries = recent_queries.filter((query) => query.input !== input);
  recent_queries.push({ input, time: Date.now(), output });
  return output;
}
