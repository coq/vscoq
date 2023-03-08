open Names
open Constr
open Libnames
open Nametab
open Printer

type completion_item = {
  ref : Names.GlobRef.t;
  path : full_path;
  typ : types;
  env : Environ.env;
  sigma : Evd.evar_map;
  mutable debug_info : string;
}

let mk_completion_item sigma ref kind env (c : constr) : completion_item = 
  {
    ref = ref;
    path = path_of_global ref;
    typ = c;
    env = env;
    sigma = sigma;
    debug_info = "";
  }

let pp_completion_item (item : completion_item) : (string * string * string) =
  let pr = pr_global item.ref in
  let name = Pp.string_of_ppcmds pr in
  let path = string_of_path item.path ^ "\n" ^ item.debug_info in
  let typ = Pp.string_of_ppcmds (pr_ltype_env item.env item.sigma item.typ) in
  (name, typ, path)