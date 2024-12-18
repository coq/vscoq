
let is_number x = try let _ = int_of_string x in true with _ -> false ;;

let main () =
  let v = Sys.argv.(1) in
  let v' = Str.(replace_first (regexp "^v") "" v) in     (* v1.20... -> 1.20... *)
  let v' = Str.(replace_first (regexp "-.*$") "" v') in  (* ...-10-fjdnfs -> ... *)
  let l = String.split_on_char '.' v' in
  (* sanitization *)
  let l =
    match l with
    | l when List.for_all is_number l -> l
    | [_] -> ["99";"99";"99"]
    | _ -> Printf.eprintf "version_parser: cannot parse: %s\n" v; exit 1 in
  let open Format in
  printf "(%a)%!" (pp_print_list ~pp_sep:(fun fmt () -> pp_print_string fmt ", ") pp_print_string) l
;;

main ()
