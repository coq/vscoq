module Pure = struct

  let string_of_ppcmds = Pp.string_of_ppcmds
  let fold_left_map = CList.fold_left_map
  
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
  
  
  let severity_of_feedback_level = let open Protocol.LspWrapper.DiagnosticSeverity in function
    | Feedback.Error -> Error
    | Feedback.Warning -> Warning
    | Feedback.(Info | Debug | Notice) -> Information
  
  let channel_of_feedback_level = let open Protocol.LspWrapper.FeedbackChannel in function
    | Feedback.Debug -> Some Debug
    | Feedback.Info -> Some Info 
    | Feedback.Notice -> Some Notice 
    | Feedback.(Error | Warning) -> None
  
end

let get_hover_contents = Hover.get_hover_contents

module CompactedDecl = Context.Compacted.Declaration

let mk_goal env sigma g =
  let EvarInfo evi = Evd.find sigma g in
  let env = Evd.evar_filtered_env env evi in
  let min_env = Environ.reset_context env in
  let id = Evar.repr g in
  let concl = match Evd.evar_body evi with
  | Evar_empty -> Evd.evar_concl evi
  | Evar_defined body -> Retyping.get_type_of env sigma body
  in
  let ccl =
    Printer.pr_letype_env ~goal_concl_style:true env sigma concl
  in
  let mk_hyp d (env,l) =
    let d' = CompactedDecl.to_named_context d in
    let env' = List.fold_right EConstr.push_named d' env in
    let hyp = Printer.pr_ecompacted_decl env sigma d in
    (env', hyp :: l)
  in
  let (_env, hyps) =
    Context.Compacted.fold mk_hyp
      (Termops.compact_named_context sigma (EConstr.named_context env)) ~init:(min_env,[]) in
  {
    Protocol.ProofState.id;
    hypotheses = List.rev_map Pure.pp_of_coqpp hyps;
    goal = Pure.pp_of_coqpp ccl;
  }

let mk_goal_diff diff_goal_map env sigma g =
  let id = Evar.repr g in
  let og_s = Proof_diffs.map_goal g diff_goal_map in
  let (hyps, ccl) = Proof_diffs.diff_goal ?og_s (Proof_diffs.make_goal env sigma g) in
  {
    Protocol.ProofState.id;
    hypotheses = List.rev_map Pure.pp_of_coqpp hyps;
    goal = Pure.pp_of_coqpp ccl;
  }

let proof_of_state st =
  match st.Vernacstate.interp.lemmas with
  | None -> None
  | Some lemmas ->
    Some (lemmas |> Vernacstate.LemmaStack.with_top ~f:Declare.Proof.get)

(* The Coq diff API is so poorly designed that we have to imperatively set a
   string option to control the behavior of `mk_goal_diff`. We do the required
   plumbing here. *)
let string_of_diff_mode = function
  | Protocol.Settings.Goals.Diff.Mode.Off -> "off"
  | On -> "on"
  | Removed -> "removed"

let set_diff_mode diff_mode =
  Goptions.set_string_option_value Proof_diffs.opt_name @@ string_of_diff_mode diff_mode

let get_proof ~previous diff_mode st =
  Vernacstate.unfreeze_full_state st;
  match proof_of_state st with
  | None -> None
  | Some proof ->
    let mk_goal env sigma g =
      match diff_mode with
      | Protocol.Settings.Goals.Diff.Mode.Off ->
        mk_goal env sigma g
      | _ ->
        begin
          set_diff_mode diff_mode;
          match Option.bind previous proof_of_state with
          | None -> mk_goal env sigma g
          | Some old_proof ->
            let diff_goal_map = Proof_diffs.make_goal_map old_proof proof in
            mk_goal_diff diff_goal_map env sigma g
        end
    in
    let env = Global.env () in
    let proof_data = Proof.data proof in
    let b_goals = Proof.background_subgoals proof in
    let sigma = proof_data.sigma in
    let goals = List.map (mk_goal env sigma) proof_data.goals in
    let unfocusedGoals = List.map (mk_goal env sigma) b_goals in
    let shelvedGoals = List.map (mk_goal env sigma) (Evd.shelf sigma) in
    let givenUpGoals = List.map (mk_goal env sigma) (Evar.Set.elements @@ Evd.given_up sigma) in
    Some {
      Protocol.ProofState.goals;
      shelvedGoals;
      givenUpGoals;
      unfocusedGoals;
    }


[%% if coq = "8.18" || coq = "8.19"  || coq = "8.20"]
let feedback_add_feeder_on_Message f =
  Feedback.add_feeder (fun fb ->
    match fb.Feedback.contents with
    | Feedback.Message(a,b,c) -> f fb.Feedback.route fb.Feedback.span_id fb.Feedback.doc_id a b [] c
    | _ -> ())
[%%else]
let feedback_add_feeder_on_Message f =
  Feedback.add_feeder (fun fb ->
    match fb.Feedback.contents with
    | Feedback.Message(a,b,c,d) -> f fb.Feedback.route fb.Feedback.span_id fb.Feedback.doc_id a b c d
    | _ -> ())
[%%endif]
let feedback_delete_feeder = Feedback.del_feeder
      