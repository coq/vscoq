{
  function errorUnclosedBracket(lb, end) {
    error("unterminated bracket '" + lb.text + "'", {start: lb.loc.start, end: end})
  } 
}

Start = TrySentence

SentenceLength
  = NoMoreSentences / Sentence {
    throw text().length;
  }

TrySentence = OneSentence / NoMoreSentences

OneSentence
  = sent:Sentence rest:$.* {
    return Object.assign(sent, {rest: rest} )    
  }

AllSentences
  = Sentence* NoMoreSentences

NoMoreSentences
  = Blank* !. { return {type: "EOF", text: text(), rest: ""} }

Sentence
  = _ sent:
    ( Bullet
    / SRequire
    / SDefinition / SInductive / SAssumption
    / SLtacDef
    / SEnd / SModuleType / SModule / SSection / SInclude
    / SAny) {
    return Object.assign(sent, {text: text()})
  }

SEnd
  = "End" __ ident:Identifier _ EndOfSentence
  { return { type: "end", ident:ident } }

SModuleType
  = "Module" __ "Type" __ ident:Identifier _ bindings:ModuleBindings? _ EndOfSentence
    { return {type: "module-type", ident:ident, bindings:bindings} }
  / "Module" __ "Type" __ ident:Identifier _ bindings:ModuleBindings? _
      moduleTypes:((":" _ id:ModuleType _ {return [id]}) / ("<:" _ id:ModuleType _ {return id})+)?
      ":=" _ expr:ModuleType
      _ EndOfSentence
    { return {type: "module-type-bind", ident:ident, bindings:bindings, expr:expr, moduleTypes: moduleTypes} }

SModule
  = "Module" intro:(__ x:$("Import"/"Export") {return x})? __ ident:Identifier _
    bindings:ModuleBindings? _
    ((":" _ ModuleType) / ("<:" _ ModuleType)+)?
    _ EndOfSentence
    { return { type: "module", intro:intro, ident:ident, bindings:bindings } }
  / "Module" __ ident:Identifier _ bindings:ModuleBindings? _
      moduleTypes:((":" _ id:ModuleType _ {return [id]}) / ("<:" _ id:ModuleType _ {return id})+)?
      ":=" _ expr:ModuleExpression
      _ EndOfSentence
    { return {type: "module-bind", ident:ident, bindings:bindings, expr:expr, moduleTypes: moduleTypes} }

SInclude
  = "Include" __ first:QualId rest:(_ "<+" _ id:QualId {return id})* _ EndOfSentence
  { return {type: "include", qualids: [first, ...rest] } }
  
SSection
  = "Section" __ ident:Identifier _ EndOfSentence
  { return { type: "section", ident:ident} }

SRequire
  = "Require" __ intro:("Import"/"Export")? modules:ModuleNameList _ EndOfSentence {
  	return { type: "require", intro: intro, modules: modules }
  }

SLtacDef
  = "Ltac" __ ident:Identifier _ (":="/"::=") _ ltac:$Command _ EndOfSentence {
  	return { type: "ltacdef", ident: ident, ltac: ltac }
  }
  
SDefinition
  = kind:DefKind __ ident:Identifier stmt:$Command _ EndOfSentence
    { return {type: "definition", kind: kind, ident: ident, stmt: stmt} }
DefKind
  = $(("Program" __)? "Lemma" / "Theorem" / "Example" / "Definition" / "Definition" / "Fixpoint")

SInductive
  = kind:IndKind _ firstBody:IndBody withBodies:(__ "with" __ id:IndBody {return id})* _ EndOfSentence
    { return {type: "inductive", kind: kind, bodies: [firstBody, ...withBodies] } }
IndKind
  = "Inductive" / "CoInductive"
IndBody
  = ident:Identifier _ ":=" _ constructors:ConstructorList
//  = ident:Identifier binders:Binders? _ ":" _ term:StuffUntilColonEquals _ ":=" _ ConstructorList
  { return {ident:ident, constructors:constructors} }
ConstructorList
  = first:("|"? _ id:ConstructorItem {return id} )
    rest:("|" _ id:ConstructorItem {return id} )*
  { return [first, ...rest] }
ConstructorItem
  = ident:Identifier binders:Binders? term:(_ ":" stuff:StuffUntilPipeOrWith { return stuff })?
  { return {ident: ident, binders: binders, term: term} }
Binders
  = Binder+
Binder
  = __ name:Name
    { return {binderType:"name", name:name} }
  / _ LBround _ name:Name type:(_ ":" _ id:StuffUntilColonEquals {return id})? _ ":=" _ term:$TermP _ RBround
    {return {binderType: "name-term", name: name, type:type, term:term} }
  / _ LBround _ first:Name rest:(__ id:Name {return id})* _ ":" _ type:$TermP _ RBround
    {return {binderType: "name-list", names: [first, ...rest], type: type } }
Name
  = ident:Identifier {return ident.text} / "_"
StuffUntilColonEquals
  = $(!(":=" / EndOfSentence) .)*
StuffUntilPipe
  = $(!("|" / EndOfSentence) .)*
StuffUntilPipeOrWith
  = $(!("|" / (__ "with" __) / EndOfSentence) .)*
StuffUntilWith
  = $(!((__ "with" __) / EndOfSentence) .)*
  
  
SAssumption
  = kind:AssumptionKind __ idents:Assumptions _ EndOfSentence
  { return {type: "assumption", kind:kind, idents:idents } }

SAny
  = Command _ EndOfSentence {return {type: "any"}}

Assumptions
  = idents:(_ LBround _ id:Assumptions RBround {return id})+
  { return Array.prototype.concat(...idents)}
  / idents:IdentifierList _ ":" typeTerm:Command
  { return idents }
AssumptionKind
  = "Axiom" / "Conjecture"
  / "Parameter" / "Parameters"
  / "Variable" / "Variables"
  / "Hypothesis" / "Hypotheses"

ModuleNameList
  = list:(_ ModuleName)+ {
    return list.map((x) => x[1])
  }

ModuleName
  = $(Identifier ("." Identifier)*)
  
ModuleType
  = qualid:("!"? QualId)
    bindings:( __ !("with" __) id:QualId {return id})*
    withBindings:( ModuleWithModule / ModuleWithDefinition )*
    { return {qualid: qualid[1], ignoreInlineDirective: qualid[0]?true:false, bindings: bindings, withBindings:withBindings} }
ModuleWithModule
  = __ "with" __  "Module" __ qualid:QualId _ ":=" _ binding:QualId
  { return { type: "module", qualid:qualid, binding:binding } }
ModuleWithDefinition
  = __ "with" __  "Definition" __ qualid:QualId _ ":=" _ binding:StuffUntilWith
  { return { type: "definition", qualid:qualid, binding:binding } }
ModuleBinding
  = _ LBround _ intro:(id:("Import"/"Export") __ {return id})? idents:IdentifierList _ ":" _ type:ModuleType _ RBround
  { return {intro:intro, idents:idents, type: type} }
ModuleBindings
  = ModuleBinding+
ModuleExpression
  = bang:"!"? qualid:QualId+
  { return {qualid:qualid, ignoreInlineDirective: bang?true:false} }

IdentifierList
  = idHd:Identifier idTl:(__ id:Identifier {return id})*
  { return [idHd, ...idTl] }
Identifier
  = (([a-zA-Z_] / UnicodeLetter) ([a-zA-Z0-9_'] / UnicodeLetter / UnicodeIdPart)*)
  { return { text: text() /*, loc: location()*/ }}

QualId
  = $(Identifier ("." Identifier)*)

EndOfSentence
  = "." IsEndOfSentence
IsEndOfSentence
  = &Blank / !.

/* hack: this does break some things... */
Term = Command
TermP = CommandP

Command
  = (_ (RoundParenCommand / SquareParenCommand / CurlyParenCommand / String / CommandText))*
/* Once we're nested, commands may have periods */
CommandP "command"
  = (_ (RoundParenCommand / SquareParenCommand / CurlyParenCommand / String / CommandTextP))*

RoundParenCommand
  = lb:LBround _
  ((CommandP _ RBround) / end:TryFindSentenceEnd { errorUnclosedBracket(lb,end) })
SquareParenCommand
  = lb:LBsquare _
  ((CommandP _ RBsquare) / end:TryFindSentenceEnd { errorUnclosedBracket(lb,end) })
CurlyParenCommand
  = lb:LBcurly _
  ((CommandP _ RBcurly) / end:TryFindSentenceEnd { errorUnclosedBracket(lb,end) })

CommandText "sentence"
  = ([^(){}[\]."] / Blank / ("." !IsEndOfSentence))+
CommandTextP
  = ([^(){}[\]"] / Blank)+

TryFindSentenceEnd
  = ([^.] / ("." !IsEndOfSentence))* { return location().end }

Bullet "bullet"
  = _ b:$( "*"+ / "+"+ / "-"+ / "{" / "}" ) {
    return { type: "bullet", bullet: b }
  }

_ "whitespace"
  = Blank* (Comment _)?

__ "whitespace"
  = Blank+ (Comment _)?

Blank "blank"
  = [ \t\n\r]

LBround = "(" ![*] {return {text: text(), loc:location()}}
RBround = ")" {return {text: text(), loc:location()}}
LBsquare = "[" {return {text: text(), loc:location()}}
RBsquare = "]" {return {text: text(), loc:location()}}
LBcurly = "{" {return {text: text(), loc:location()}}
RBcurly = "}" {return {text: text(), loc:location()}}
LBc = "(*"
RBc = "*)"

Comment "comment"
  = LBc CommentText RBc

CommentText "commentText"
  = (String / Comment / ([^"*(] / ("(" !"*") / ("*" !")"))+ )*
  
 UnicodeLetter
  = [a-z]
 UnicodeIdPart
  = [a-z]

String "string"
  = ["] ([^"] / "\"\"")* ["]
