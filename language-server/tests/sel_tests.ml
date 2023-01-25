open Base
open Sel

let%test_unit "wait.empty" =
  let (ready, remaining) = Sel.wait [] in
  [%test_eq: bool] (List.is_empty ready) true;
  [%test_eq: bool] (List.is_empty remaining) true

let%test_unit "wait.emptyqueue" =
  let q = Stdlib.Queue.create () in
  let (ready, remaining) = Sel.wait ~stop_after_being_idle_for:1.0 [Sel.on_queue q (fun () -> ())] in
  [%test_eq: bool] (List.is_empty ready) true;
  [%test_eq: bool] (List.is_empty remaining) false;
  Stdlib.Queue.push () q;
  let (ready, remaining) = Sel.wait [Sel.on_queue q (fun () -> ())] in
  [%test_eq: bool] (List.is_empty ready) false;
  [%test_eq: bool] (List.is_empty remaining) true
