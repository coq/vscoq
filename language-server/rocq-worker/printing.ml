
let rec regroup_tags_aux acc = function
| [] -> acc
| hd :: tl ->
  match Pp.repr hd with
  | Pp.Ppcmd_glue l ->
    let acc = regroup_tags_aux acc l in
    regroup_tags_aux acc tl
  | Pp.Ppcmd_tag (s, pp) when String.starts_with ~prefix:Pp.start_pfx s ->
    let pp = regroup_tags [pp] in
    regroup_tags_aux (pp::acc) tl
  | Pp.Ppcmd_tag (s, pp) when String.starts_with ~prefix:Pp.end_pfx s ->
    let pp = regroup_tags [pp] in
    let n = String.length Pp.end_pfx in
    let tag = String.sub s n (String.length s - n) in
    begin match acc with
    | acc0::acc1::tlacc ->
      let acc1 = Pp.tag tag (Pp.seq ((List.rev acc0) @ pp)) :: acc1 in
      regroup_tags_aux (acc1 :: tlacc) tl
    | _ -> failwith ("extra closing tag: " ^ tag)
    end
  | _ ->
    let acc = (hd::List.hd acc)::List.tl acc in
    regroup_tags_aux acc tl

and regroup_tags l =
match regroup_tags_aux [[]] l with [l] -> List.rev l | _ -> failwith "tag not closed"

let block_of_coqblock = let open Protocol.Printing in function
| Pp.Pp_hbox -> Pp_hbox
| Pp.Pp_hovbox x -> Pp_hovbox x
| Pp.Pp_hvbox x -> Pp_hvbox x
| Pp.Pp_vbox x -> Pp_vbox x 

let rec pp_of_coqpp t = let open Protocol.Printing in match Pp.repr t with
| Pp.Ppcmd_empty -> Ppcmd_empty
| Pp.Ppcmd_string s -> Ppcmd_string s
| Pp.Ppcmd_glue l -> (* We are working around a Coq hack here *)
  let l = regroup_tags l in
  Ppcmd_glue (List.map pp_of_coqpp l)
| Pp.Ppcmd_box (bt, pp) -> Ppcmd_box (block_of_coqblock bt, pp_of_coqpp pp)
| Pp.Ppcmd_tag (tag, pp) -> Ppcmd_tag (tag, pp_of_coqpp pp)
| Pp.Ppcmd_print_break (m,n) -> Ppcmd_print_break (m,n)
| Pp.Ppcmd_force_newline -> Ppcmd_force_newline
| Pp.Ppcmd_comment l -> Ppcmd_comment l
