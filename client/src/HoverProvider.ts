'use strict';
import * as vscode from 'vscode';
import { CoqProject } from './CoqProject';
import * as editorAssist from './EditorAssist';

// Inputs to ignore when calling hover
const excludes = [''];

function operatorRegex(str: string) {
  // Matching operators is simple, as Coq will kindly
  // print spaces before and after them,
  // we use lookahead/lookbehind to avoid catching them
  return new RegExp("(?<=\\s)" + str + "(?=\\s)", "g");
}

// Format a Coq type to be pretty and compact (e.g. replace forall with ∀)
function compactify(str: string) {
  const replaces = [
    { match: /\bfun\b/g, subst: "λ" },
    { match: /\bforall\b/g, subst: "∀" },
    { match: /\bexists\b/g, subst: "∃" },
    { match: operatorRegex("\\\\\\/"), subst: "∨" },
    { match: operatorRegex("\\/\\\\"), subst: "∧" },
    { match: operatorRegex("<->"), subst: "↔" },
    { match: operatorRegex("->"), subst: "→" },
    { match: operatorRegex("<="), subst: "≤" },
    { match: operatorRegex(">="), subst: "≥" },
    { match: operatorRegex("=>"), subst: "⇒" },
    { match: operatorRegex("<>"), subst: "≠" },
    { match: operatorRegex("~"), subst: "¬" }
  ];
  for (const replace of replaces) {
    str = str.replace(replace.match, replace.subst);
  }
  return str;
}

function formatCheck(response: string) {
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

  if (type === "") return;
  type = compactify(type);

  let hover = [{ language: "coq", value: type }];
  // if (where)
  //  hover.push({language:"coq", value:where});
  return new vscode.Hover(hover);
}

function findClosingParenthese(str: string, start: number) {
  let depth = 0;
  for (let i = start; i < str.length; i++) {
    if (str[i] === "(") depth++;
    if (str[i] === ")") depth--;
    if (depth < 0) return i;
  }
  return null;
}

function formatLocate(response: string) {
  response = response.trim()
  if (response === "Unknown notation") return;
  const notationRegex = /^(Reserved\s+)?Notation\s*"(.*?)"\s*:=\s*\(/gms;
  const matches = response.matchAll(notationRegex)
  if (!matches) return;

  let hover = [];
  for (const match of matches) {
    if (match.index === undefined) continue;
    const notation = match[2];
    const begin = match.index + match[0].length;
    const end = findClosingParenthese(response, begin);
    if (end === null) continue;
    const definition = compactify(response.slice(begin, end));
    hover.push({ language: "coq", value: `"${notation}" := ${definition}` })
  }
  return new vscode.Hover(hover);
}

// Perform a query to get hover text
async function query(query: "check" | "locate", text: string, project: CoqProject, document: vscode.TextDocument) {
  const doc = project.getOrCurrent(document.uri.toString());
  if (!doc) return;
  const response = await doc.hoverQuery(query, text);
  return response;
}

// VSCode calls HoverProvider repeatedly
// So we memoize recent results to avoid having to requery
type query_result = { input: string, time: number, output: vscode.Hover };

let recent_queries: query_result[] = [];
const query_redo_delay = 2000; // milliseconds

function filterOld(query: query_result) {
  return Date.now() - query.time <= query_redo_delay;
}

export const regExpCoqNotation = /[^\p{Z}\p{C}"]+/u;

export function coqIdOrNotationFromRange(document: vscode.TextDocument, range: vscode.Range | undefined) {
  let text = document.getText(range);
  if (new RegExp("\^" + regExpCoqNotation.source + "\$", regExpCoqNotation.flags).test(text)
    && !new RegExp("\^" + editorAssist.regExpQualifiedCoqIdent.source + "\$", regExpCoqNotation.flags).test(text))
    return "\"" + text + "\"";
  return text;
}

async function query_input(input: string, project: CoqProject, document: vscode.TextDocument) {
  let is_notation = input[0] === "\"";

  // § Check if query was recently performed
  recent_queries = recent_queries.filter(filterOld);
  const has_query = recent_queries.filter((query) => query.input === input)[0];
  if (has_query)
    return has_query.output;

  // § if not, perform query
  const method = is_notation ? "locate" : "check";
  let response = await query(method, input, project, document);
  if (!response && !is_notation) {
    // Something that looks like an identifier might in fact be a notation
    response = await query("locate", `"${input}"`, project, document);
    is_notation = true;
  }

  if (!response) return;
  const output = is_notation ? formatLocate(response) : formatCheck(response);
  if (!output) return;

  // § Add query to recent queries
  recent_queries.push({ input, time: Date.now(), output });
  return output;
}

export async function provideHover(position: vscode.Position, project: CoqProject, document: vscode.TextDocument) {
  // § Get text under cursor
  const ranges =
    [
      // match largest non-space segment
      document.getWordRangeAtPosition(position, /\S+/),
      // match identifier
      document.getWordRangeAtPosition(position, editorAssist.regExpQualifiedCoqIdent),
      // match symbols
      document.getWordRangeAtPosition(position, regExpCoqNotation),
    ];

  for (const range of ranges) {
    if (range === undefined) continue;
    const input = coqIdOrNotationFromRange(document, range).trim();
    if (excludes.includes(input)) continue;

    const hover = await query_input(input, project, document);
    if (hover !== undefined) return hover;
  }
  return;
}
