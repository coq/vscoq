import * as vscode from 'vscode';
import {CoqLanguageServer} from './CoqLanguageServer';


interface TriggerSnippet {
  label:string,
  insertText: string,
  completion?: vscode.CompletionItem[],
  detail?: string,
}

type Snippet = string | {label: string, insertText: string, documentation?: string};


function snippetSentence(item: Snippet) : vscode.CompletionItem {
  if(typeof item === 'string') { 
    const result = new vscode.CompletionItem(item,vscode.CompletionItemKind.Snippet);
    result.insertText = item + ".";
    return result;
  } else {
    const result = new vscode.CompletionItem(item.label,vscode.CompletionItemKind.Snippet);
    result.insertText = new vscode.SnippetString(item.insertText);
    result.documentation = item.documentation as string; // vscode needs to provide stricter types in its API...
    return result;
  }
}


const optionsSnippetsRaw = [
  "Asymmetric Patterns",
  "Atomic Load",
  "Automatic Coercions Import",
  "Automatic Introduction",
  "Boolean Equality Schemes",
  "Bracketing Last Introduction Pattern",
  "Case Analysis Schemes",
  "Compat Notations",
  "Congruence Depth",
  "Congruence Verbose",
  "Contextual Implicit",
  "Debug Auto",
  "Debug Eauto",
  "Debug RAKAM",
  "Debug Tactic Unification",
  "Debug Trivial",
  "Debug Unification",
  "Decidable Equality Schemes",
  "Default Clearing Used Hypotheses",
  "Dependent Propositions Elimination",
  "Discriminate Introduction",
  "Dump Bytecode",
  "Elimination Schemes",
  "Equality Scheme",
  "Extraction AutoInline",
  "Extraction Conservative Types",
  "Extraction KeepSingleton",
  "Extraction Optimize",
  "Extraction SafeImplicits",
  "Extraction TypeExpand",
  "Hide Obligations",
  "Implicit Arguments",
  "Info Auto",
  "Info Eauto",
  "Info Trivial",
  "Injection L2R Pattern Order",
  "Injection On Proofs",
  "Intuition Iff Unfolding",
  "Intuition Negation Unfolding",
  "Kernel Term Sharing",
  "Keyed Unification",
  "Maximal Implicit Insertion",
  "Nonrecursive Elimination Schemes",
  "Parsing Explicit",
  "Primitive Projections",
  "Printing All",
  "Printing Coercions",
  "Printing Existential Instances",
  "Printing Implicit",
  "Printing Implicit Defensive",
  "Printing Matching",
  "Printing Notations",
  "Printing Primitive Projection Compatibility",
  "Printing Primitive Projection Parameters",
  "Printing Projections",
  "Printing Records",
  "Printing Synth",
  "Printing Universes",
  "Printing Wildcard",
  "Program Mode",
  "Proof Using Clear Unused",
  "Record Elimination Schemes",
  "Regular Subst Tactic",
  "Reversible Pattern Implicit",
  "Rewriting Schemes",
  "Short Module Printing",
  "Shrink Obligations",
  "SimplIsCbn",
  "Standard Proposition Elimination Names",
  "Strict Implicit",
  "Strict Proofs",
  "Strict Universe Declaration",
  "Strongly Strict Implicit",
  "Suggest Proof Using",
  "Tactic Compat Context",
  "Tactic Evars Pattern Unification",
  "Transparent Obligations",
  "Typeclass Resolution After Apply",
  "Typeclass Resolution For Conversion",
  "Typeclasses Debug",
  "Typeclasses Dependency Order",
  "Typeclasses Modulo Eta",
  "Typeclasses Strict Resolution",
  "Typeclasses Unique Instances",
  "Typeclasses Unique Solutions",
  "Universal Lemma Under Conjunction",
  "Universe Minimization ToSet",
  "Universe Polymorphism",
  "Verbose Compat Notations"
  ];

const optionsSnippets = [
  ...optionsSnippetsRaw,
  "Bullet Behavior",
  "Default Goal Selector",
  "Default Proof Mode",
  "Default Proof Using",
  "Default Timeout",
  "Extraction File Comment",
  "Extraction Flag",
  "Firstorder Depth",
  "Hyps Limit",
  "Info Level",
  "Inline Level",
  "Loose Hint Behavior",
  "Printing Depth",
  "Printing Width",
  "Typeclasses Depth",
  ].map(snippetSentence);;
const setOptionsSnippets = [
  ...optionsSnippetsRaw,
  {label: "Bullet Behavior", insertText: "Bullet Behavior \"${1|None,Strict Subproofs|}\"."},
  {label: "Default Goal Selector", insertText: "Default Goal Selector \"${1:selector}\"."},
  {label: "Default Proof Mode", insertText: "Default Proof Mode \"${1|Classic,Noedit,Ltac2|}\"."},
  {label: "Default Proof Using", insertText: "Default Proof Using \"${1:section_var_expr}\"."},
  {label: "Default Timeout", insertText: "Default Timeout ${1:num}."},
  {label: "Extraction File Comment", insertText: "Extraction File Comment \"${1:string}\"."},
  {label: "Extraction Flag", insertText: "Extraction Flag ${1:num}."},
  {label: "Firstorder Depth", insertText: "Firstorder Depth ${1:num}."},
  {label: "Hyps Limit", insertText: "Hyps Limit ${1:num}."},
  {label: "Info Level", insertText: "Info Level ${1:num}."},
  {label: "Inline Level", insertText: "Inline Level ${1:num}."},
  {label: "Loose Hint Behavior", insertText: "Loose Hint Behavior \"${1|Lax,Warn,Strict|}\"."},
  {label: "Printing Depth", insertText: "Printing Depth ${1:num}."},
  {label: "Printing Width", insertText: "Printing Width ${1:num}."},
  {label: "Typeclasses Depth", insertText: "Typeclasses Depth ${1:num}."},
  ].map(snippetSentence);

const printSnippets = [
  "All",
  {label: "All Dependencies", insertText: "All Dependencies ${1:qualid}."},
  {label: "Assumptions", insertText: "Assumptions ${1:qualid}."},
  "Canonical Projections",
  "Classes",
  {label: "Coercion Paths", insertText: "Coercion Paths ${1:class1} ${2:class2}."},
  "Coercions",
  "Extraction Inline",
  "Fields",
  {label: "Grammar", insertText: "Grammar ${1|constr,pattern|}."},
  "Graph",
  {label: "Hint", insertText: "Hint ${1:ident}."},
  "Hint *",
  {label: "HintDb", insertText: "HintDb ${1:ident}."},
  {label: "Implicit", insertText: "Implicit ${1:qualid}."},
  "Libraries",
  "LoadPath",
  {label: "Ltac", insertText: "Ltac ${1:qualid}."},
  "ML Modules",
  "ML Path",
  {label: "Module", insertText: "Module ${1:ident}."},
  {label: "Module Type", insertText: "Module Type ${1:ident}."},
  {label: "Opaque Dependencies", insertText: "Opaque Dependencies ${1:qualid}."},
  "Options",
  "Rings",
  {label: "Scope", insertText: "Scope ${1:scope}."},
  "Scopes",
  {label: "Section", insertText: "Section ${1:ident}."},
  "Sorted Universes",
  {label: "Sorted Universes (filename)", insertText: "Sorted Universes \"${1:filename}\"."},
  "Strategies",
  {label: "Strategy", insertText: "Strategy ${1:qualid}."},
  {label: "Table", insertText: "Table ${1|Printing If,Printing Let|}."},
  "Tables",
  {label: "Term", insertText: "Term ${1:qualid}."},
  {label: "Transparent Dependencies", insertText: "Transparent Dependencies ${1:qualid}."},
  "Universes",
  {label: "Universes (filename)", insertText: "Universes \"${1:filename}\"."},
  "Visibility",
].map(snippetSentence);

const showSnippets = [
  {label: "(num)", insertText: "${1:num}.", documentation: "Displays only the num-th subgoal"},
  "Conjecturest",
  "Existentials",
  "Intro",
  "Intros",
  "Proof",
  "Script",
  "Universes",
].map(snippetSentence);

const hintSnippets = [
  {label: "(definition)", insertText: "${1:definition} : ${2:idents …}."},
  {label: "Constructors", insertText: "Constructors ${1:idents …} : ${2:idents …}."},
  {label: 'Cut', insertText: 'Cut "${1:regexp}" : ${2:idents …}.'},
  {label: 'Extern', insertText: 'Extern ${1:num} ${2:optional-pattern} => ${3:tactic} : ${4:idents …}.'},
  {label: 'Immediate', insertText: 'Immediate ${1:term} : ${2:idents …}.'},
  {label: 'Mode', insertText: 'Mode ${1:qualid} ${2:(+|-|!)+} : ${3:idents …}.'},
  {label: 'Opaque', insertText: 'Opaque ${1:qualid} : ${2:idents …}.'},
  {label: 'Resolve', insertText: 'Resolve ${1:term} : ${2:idents …}.'},
  {label: 'Rewrite', insertText: 'Rewrite ${1:terms …} : ${2:idents …}.'},
  {label: 'Rewrite ->', insertText: 'Rewrite -> ${1:terms …} : ${2:idents …}.'},
  {label: 'Rewrite <-', insertText: 'Rewrite <- ${1:terms …} : ${2:idents …}.'},
  {label: 'Transparent', insertText: 'Transparent ${1:qualid} : ${2:idents …}.'},
  {label: 'Unfold', insertText: 'Unfold ${1:qualid} : ${2:idents …}.'},
].map(snippetSentence);


const triggerSnippets : TriggerSnippet[] = [
  {label: "Set...", insertText: "Set ", completion: setOptionsSnippets, detail: "Set coqtop options"},
  {label: "Unset...", insertText: "Unset ", completion: optionsSnippets, detail: "Unset coqtop options"},
  {label: "Local Set...", insertText: "Local Set ", completion: setOptionsSnippets},
  {label: "Global Unset...", insertText: "Global Unset ", completion: optionsSnippets},
  {label: "Test...", insertText: "Test ", completion: optionsSnippets},
  {label: "Print...", insertText: "Print ", completion: printSnippets},
  {label: "Show...", insertText: "Show ", completion: showSnippets},
  {label: "Hint...", insertText: "Hint ", completion: hintSnippets},
  {label: "Local Hint...", insertText: "Local Hint ", completion: hintSnippets},
  {label: "Global Hint...", insertText: "Global Hint ", completion: hintSnippets},
  {label: "Export Hint...", insertText: "#[export] Hint ", completion: hintSnippets},
  {label: "Arguments", insertText: "Arguments ${1:qualid} ${2:possibly_bracketed_idents …}."},
  {label: "Local Arguments", insertText: "Local Arguments ${1:qualid} ${2:possibly_bracketed_idents …}."},
  {label: "Global Arguments", insertText: "Global Arguments ${1:qualid} ${2:possibly_bracketed_idents …}."},
  ];

let triggerRegexp : RegExp;

function getTriggerSnippet(str: string) : TriggerSnippet|null {
  const match = triggerRegexp.exec(str);
  if(match && match.length > 1) {
    match.shift();
    const triggerIdx = match.findIndex((v) => v!==undefined)
    return triggerSnippets[triggerIdx];
  } else
    return null;
}

function getTriggerCompletions(prefix: string) {
  const triggerCompletions = new vscode.CompletionList(
    triggerSnippets
    .filter((trigger) => {
      return trigger.insertText.startsWith(prefix);
    })
    .map((trigger) => {
      const item = new vscode.CompletionItem(trigger.label);
      item.insertText = new vscode.SnippetString(trigger.insertText);
      item.detail = trigger.detail as string; // vscode needs to update its API
      if(trigger.completion)
        item.command = {
          command: "editor.action.triggerSuggest",
          title: "Trigger Suggest",
          arguments: [vscode.window.activeTextEditor]
        }
      return item;
    }), true);
  return triggerCompletions;
}

export function setupSnippets(subscriptions: vscode.Disposable[]) {
  triggerRegexp = RegExp(`\\s*(?:${triggerSnippets.map((v) => "(" + escapeRegExp(v.insertText) + ")").join('|')})\\s*$`);

  const triggerTerminators = triggerSnippets.map((trigger) => trigger.insertText[trigger.insertText.length-1]);

  // Set-Options snippets are registered manually because coq.json snippets
  // don't currently provide a nice interaction.
  subscriptions.push(vscode.languages.registerCompletionItemProvider('coq', {
    provideCompletionItems: async (doc, pos, token) => {
      try {
        const prefix = await (await CoqLanguageServer.getInstance().getPrefixText(doc.uri.toString(),pos,token)).trimStart();        

        if(prefix === "")
          return [];
        const trigger = getTriggerSnippet(prefix);
        if(trigger)
          return trigger.completion;
        else
          return getTriggerCompletions(prefix.trim());
      } catch(err) {
        return [];
      }
    }
  }, ...triggerTerminators));

  // const qedCompletion = new vscode.CompletionItem("Qed.", vscode.CompletionItemKind.Snippet);
  // const definedCompletion = new vscode.CompletionItem("Defined.", vscode.CompletionItemKind.Snippet);
  // const admittedCompletion = new vscode.CompletionItem("Admitted.", vscode.CompletionItemKind.Snippet);
  // const outdentCompletions = [qedCompletion, definedCompletion, admittedCompletion];
  // subscriptions.push(vscode.languages.registerCompletionItemProvider('coq', {
  //   provideCompletionItems: async (doc, pos, token) => {
  //     try {
  //       const line = doc.lineAt(pos.line);

  //       // outdent the text
  //       const indentSize = getIndentSize(doc);
  //       const insertLine = {command: "editor.action.insertLineAfter", arguments: [], title: "insert line"};
  //       const outdentRange = new vscode.Range(line.lineNumber, Math.max(0,line.firstNonWhitespaceCharacterIndex-indentSize), line.lineNumber, line.firstNonWhitespaceCharacterIndex);
  //       const outdent = new vscode.TextEdit(outdentRange, '');
  //       outdentCompletions.forEach(o => {
  //         o.additionalTextEdits = [outdent];
  //         o.command = insertLine;
  //       });
  //       return outdentCompletions;
  //     } catch(err) {
  //       return [];
  //     }
  //   }
  // }));


}

// function getIndentSize(doc: vscode.TextDocument) : number {
//   let editor = vscode.window.activeTextEditor;
//   if(editor && editor.document.uri === doc.uri)
//     return editor.options.insertSpaces ? +editor.options.tabSize : 1;
//   editor = vscode.window.visibleTextEditors.find((e) => e.document.uri === doc.uri);
//   if(editor && editor.document.uri === doc.uri)
//     return editor.options.insertSpaces ? +editor.options.tabSize : 1;
//   else
//     return 0;
// }

/** see: http://stackoverflow.com/questions/3446170/escape-string-for-use-in-javascript-regex */
function escapeRegExp(str : string) {
  return str.replace(/[\-\[\]\/\{\}\(\)\*\+\?\.\\\^\$\|]/g, "\\$&");
}

