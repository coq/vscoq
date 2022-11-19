(* source: https://github.com/coq-community/vscoq/issues/164 *)
Set Diffs "on"
Require Vector Fin.
Notation " [| x ; y ; .. ; z |] " := (Vector.cons _ x _ (Vector.cons _ y _ .. (Vector.cons _ z _ (Vector.nil _)) ..)).

Lemma bug164 : { n12 & { n13 & Vector.t (Fin.t (1 +  (S (S (S n12))))) n13}}.
Proof.
  do 2 eexists. 
  exact ([|Fin.F1;Fin.L 3 (Fin.R 1 Fin.F1)|]). (*The diff-output does not make any sense*)