Require Import P04.


Check rev_involutive : forall l : natlist,
  rev ((rev l)) = l.
