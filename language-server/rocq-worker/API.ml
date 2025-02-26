module Pure = struct

  let string_of_ppcmds = Pp.string_of_ppcmds
  let fold_left_map = CList.fold_left_map
    
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

let get_proof = ProofState.get_proof


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
      