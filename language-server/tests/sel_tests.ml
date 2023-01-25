open Base
open Sel

(*
let%test_unit "wait.empty" =
  let (ready, remaining) = Sel.wait [] in
  [%test_eq: bool] (List.is_empty ready) true;
  [%test_eq: bool] (List.is_empty remaining) true
*)