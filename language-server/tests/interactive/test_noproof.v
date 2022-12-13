(* jump to the bottom, then come up, change the value of x and go back to the bottom *)

Definition x := 2.

Print bool.

Definition t := 3 + x.

Eval compute in t.