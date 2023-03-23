Require Export P01.


(** Prove the following claim, marking cases (and subcases) with
    bullets when you use [destruct]. *)

Print xorb.

Theorem xorb_to_andb : forall b c : bool,
  xorb b c = true -> andb b c = false.
Proof.
  exact FILL_IN_HERE.
Qed.

