(**************************************************************************)
(*                                                                        *)
(*                                 VSCoq                                  *)
(*                                                                        *)
(*                   Copyright INRIA and contributors                     *)
(*       (see version control and README file for authors & dates)        *)
(*                                                                        *)
(**************************************************************************)
(*                                                                        *)
(*   This file is distributed under the terms of the MIT License.         *)
(*   See LICENSE file.                                                    *)
(*                                                                        *)
(**************************************************************************)
open Names
open Printer
open Pp

let md_code_block s =
  Format.sprintf "```coq\n%s\n```" s

(* Format a Coq type to be pretty and compact (e.g. replace forall with ∀) *)
let compactify s =
  let replacements = [
    Str.regexp {|\bfun\b|}, "λ";
    Str.regexp {|\bforall\b|}, "∀";
    Str.regexp {|\bexists\b|}, "∃";
    Str.regexp {| \\/ |}, " ∨ ";
    Str.regexp {| /\\ |}, " ∧ ";
    Str.regexp {| <-> |}, " ↔ ";
    Str.regexp {| -> |}, " → ";
    Str.regexp {| <= )|}, " ≤ ";
    Str.regexp {| >= )|}, " ≥ ";
    Str.regexp {| => )|}, " ⇒ ";
    Str.regexp {| <> )|}, " ≠ ";
    Str.regexp {| ~ )|}, " ¬ "
  ]
  in
  List.fold_left (fun s (reg,repl) -> Str.global_replace reg repl s) s replacements

(* TODO this should be exposed by Coq and removed from here *)
let pr_args args more_implicits mods =
  let open Vernacexpr in
  let pr_s = prlist (fun CAst.{v=s} -> str "%" ++ str s) in
  let pr_if b x = if b then x else str "" in
  let pr_one_arg (x,k) = pr_if k (str"!") ++ Name.print x in
  let pr_br imp force x =
    let left,right =
      match imp with
      | Glob_term.NonMaxImplicit -> str "[", str "]"
      | Glob_term.MaxImplicit -> str "{", str "}"
      | Glob_term.Explicit -> if force then str"(",str")" else mt(),mt()
    in
    left ++ x ++ right
  in
  let get_arguments_like s imp tl =
    if s = [] && imp = Glob_term.Explicit then [], tl
    else
      let rec fold extra = function
        | RealArg arg :: tl when
            List.equal (fun a b -> String.equal a.CAst.v b.CAst.v) arg.notation_scope s
            && arg.implicit_status = imp ->
          fold ((arg.name,arg.recarg_like) :: extra) tl
        | args -> List.rev extra, args
      in
      fold [] tl
  in
  let rec print_arguments = function
    | [] -> mt()
    | VolatileArg :: l -> spc () ++ str"/" ++ print_arguments l
    | BidiArg :: l -> spc () ++ str"&" ++ print_arguments l
    | RealArg { name = id; recarg_like = k;
                notation_scope = s;
                implicit_status = imp } :: tl ->
      let extra, tl = get_arguments_like s imp tl in
      spc() ++ hov 1 (pr_br imp (extra<>[]) (prlist_with_sep spc pr_one_arg ((id,k)::extra)) ++
      pr_s s) ++ print_arguments tl
  in
  let rec print_implicits = function
    | [] -> mt ()
    | (name, impl) :: rest ->
      spc() ++ pr_br impl false (Name.print name) ++ print_implicits rest
  in
  print_arguments args ++
  if not (CList.is_empty more_implicits) then
    prlist (fun l -> str"," ++ print_implicits l) more_implicits
  else (mt ()) ++
       (if not (CList.is_empty mods) then str" : " else str"") ++
       prlist_with_sep (fun () -> str", " ++ spc()) (function
           | `ReductionDontExposeCase -> str "simpl nomatch"
           | `ReductionNeverUnfold -> str "simpl never"
           | `DefaultImplicits -> str "default implicits"
           | `Rename -> str "rename"
           | `Assert -> str "assert"
           | `ExtraScopes -> str "extra scopes"
           | `ClearImplicits -> str "clear implicits"
           | `ClearScopes -> str "clear scopes"
           | `ClearBidiHint -> str "clear bidirectionality hint")
         mods

let implicit_kind_of_status = function
  | None -> Anonymous, Glob_term.Explicit
  | Some ((na,_,_),_,(maximal,_)) -> na, if maximal then Glob_term.MaxImplicit else Glob_term.NonMaxImplicit

let extra_implicit_kind_of_status imp =
  let _,imp = implicit_kind_of_status imp in
  (Anonymous, imp)

let needs_extra_scopes ref scopes =
  let open Constr in
  let rec aux env t = function
    | [] -> false
    | _::scopes -> match kind (Reduction.whd_all env t) with
      | Prod (na,dom,codom) -> aux (Environ.push_rel (Context.Rel.Declaration.LocalAssum (na,dom)) env) codom scopes
      | _ -> true
  in
  let env = Global.env() in
  let ty, _ctx = Typeops.type_of_global_in_context env ref in
  aux env ty scopes

let rec main_implicits i renames recargs scopes impls =
  if renames = [] && recargs = [] && scopes = [] && impls = [] then []
  else
    let recarg_like, recargs = match recargs with
      | j :: recargs when i = j -> true, recargs
      | _ -> false, recargs
    in
    let (name, implicit_status) =
      match renames, impls with
      | _, (Some _ as i) :: _ -> implicit_kind_of_status i
      | name::_, _ -> (name,Glob_term.Explicit)
      | [], (None::_ | []) -> (Anonymous, Glob_term.Explicit)
    in
    let notation_scope = match scopes with
      | scope :: _ -> List.map CAst.make scope
      | [] -> []
    in
    let status = {Vernacexpr.implicit_status; name; recarg_like; notation_scope} in
    let tl = function [] -> [] | _::tl -> tl in
    (* recargs is special -> tl handled above *)
    let rest = main_implicits (i+1) (tl renames) recargs (tl scopes) (tl impls) in
    status :: rest

let dummy = {
  Vernacexpr.implicit_status = Glob_term.Explicit;
   name = Anonymous;
   recarg_like = false;
   notation_scope = [];
 }

let is_dummy = function
  | Vernacexpr.(RealArg {implicit_status; name; recarg_like; notation_scope}) ->
    name = Anonymous && not recarg_like && notation_scope = [] && implicit_status = Glob_term.Explicit
  | _ -> false

let rec insert_fake_args volatile bidi impls =
  let open Vernacexpr in
  match volatile, bidi with
  | Some 0, _ -> VolatileArg :: insert_fake_args None bidi impls
  | _, Some 0 -> BidiArg :: insert_fake_args volatile None impls
  | None, None -> List.map (fun a -> RealArg a) impls
  | _, _ ->
    let hd, tl = match impls with
      | impl :: impls -> impl, impls
      | [] -> dummy, []
    in
    let f = Option.map pred in
    RealArg hd :: insert_fake_args (f volatile) (f bidi) tl

let print_arguments ref =
  let flags, recargs, nargs_for_red =
    let open Reductionops.ReductionBehaviour in
    match get ref with
    | None -> [], [], None
    | Some NeverUnfold -> [`ReductionNeverUnfold], [], None
    | Some (UnfoldWhen { nargs; recargs }) -> [], recargs, nargs
    | Some (UnfoldWhenNoMatch { nargs; recargs }) -> [`ReductionDontExposeCase], recargs, nargs
  in
  let names, not_renamed =
    try Arguments_renaming.arguments_names ref, false
    with Not_found ->
      let env = Global.env () in
      let ty, _ = Typeops.type_of_global_in_context env ref in
      List.map Util.pi1 (Impargs.compute_implicits_names env (Evd.from_env env) (EConstr.of_constr ty)), true in
  let scopes = Notation.find_arguments_scope ref in
  let flags = if needs_extra_scopes ref scopes then `ExtraScopes::flags else flags in
  let impls = Impargs.extract_impargs_data (Impargs.implicits_of_global ref) in
  let impls, moreimpls = match impls with
    | (_, impls) :: rest -> impls, rest
    | [] -> assert false
  in
  let impls = main_implicits 0 names recargs scopes impls in
  let moreimpls = List.map (fun (_,i) -> List.map extra_implicit_kind_of_status i) moreimpls in
  let bidi = Pretyping.get_bidirectionality_hint ref in
  let impls = insert_fake_args nargs_for_red bidi impls in
  if List.for_all is_dummy impls && moreimpls = [] && flags = [] then mt ()
  else
    pr_args impls moreimpls flags ++
     (if not_renamed then mt () else
      fnl () ++ str "  (where some original arguments have been renamed)")

let canonical_name_info ref =
  let cref = Globnames.canonical_gr ref in
  if GlobRef.UserOrd.equal ref cref then mt ()
  else match Nametab.path_of_global cref with
    | path -> spc() ++ str "(syntactically equal to" ++ spc() ++ Libnames.pr_path path ++ str ")"
    | exception Not_found -> spc() ++ str "(missing canonical, bug?)"

(* End of imported Coq code *)

let pr_globref_kind = let open GlobRef in function
  | ConstRef _ -> "Constant"
  | IndRef _ -> "Inductive"
  | ConstructRef _ -> "Constructor"
  | VarRef _ -> "Variable"

let ref_info env _sigma ref udecl =
  let typ, _univs = Typeops.type_of_global_in_context env ref in
  let bl = Printer.universe_binders_with_opt_names (Environ.universes_of_global env ref) udecl in
  let sigma = Evd.from_ctx (UState.of_names bl) in
  let typ = Arguments_renaming.rename_type typ ref in
  let impargs = Impargs.select_stronger_impargs (Impargs.implicits_of_global ref) in
  let impargs = List.map Impargs.binding_kind_of_status impargs in
  let typ = pr_ltype_env env sigma ~impargs typ in
  let path = Libnames.pr_path (Nametab.path_of_global ref) ++ canonical_name_info ref in
  let args = print_arguments ref in
  let args = if Pp.ismt args then [] else ["**Args:** " ^ (Pp.string_of_ppcmds (print_arguments ref))] in
  String.concat "\n" @@ [md_code_block @@ compactify @@ Pp.string_of_ppcmds typ]@args@
  [Format.sprintf "**%s** %s" (pr_globref_kind ref) (Pp.string_of_ppcmds path)]

let mod_info mp =
  md_code_block @@ Format.sprintf "Module %s" (DirPath.to_string (Nametab.dirpath_of_module mp))

let modtype_info mp =
  md_code_block @@ Format.sprintf "Module Type %s" (Libnames.string_of_path (Nametab.path_of_modtype mp))

let syndef_info kn =
  md_code_block @@ Format.sprintf "Notation %s" (Libnames.string_of_path (Nametab.path_of_abbreviation kn))

let get_hover_contents env sigma ref_or_by_not =
  match ref_or_by_not.CAst.v with
  | Constrexpr.AN qid ->
    let r = begin try
      let udecl = None in
      let ref = Nametab.locate qid in
      Some (ref_info env sigma ref udecl)
    with Not_found ->
    try
      let kn = Nametab.locate_abbreviation qid in
      Some (syndef_info kn)
    with Not_found ->
    try
      let mp = Nametab.locate_module qid in
      Some (mod_info mp)
    with Not_found ->
    try
      let mp = Nametab.locate_modtype qid in
      Some (modtype_info mp)
    with Not_found ->
      None
    end
    in
    Option.map Lsp.Types.(fun value -> MarkupContent.create ~kind:MarkupKind.Markdown ~value) r
  | Constrexpr.ByNotation (_ntn,_sc) -> assert false