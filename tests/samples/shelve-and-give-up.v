Require Import Lia.

Lemma ajksdfl (a : nat) : a < a + 3 /\ a < a + 5.
Proof.
  assert (H: a < a + 1 + 1).
  { simpl. }
  split.
  - lia.
  - assert (H1 : 5 = 3 + 2).
    { lia. }
    rewrite H1.
    shelve.
  Unshelve.
  lia.