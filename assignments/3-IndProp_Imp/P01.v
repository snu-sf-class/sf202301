Require Export D.
Export Natord.
Require Export Tactics. 

Theorem ev_sum_not : forall n m, ev (n + m) -> not (ev n) -> not (ev m).
Proof.
  exact FILL_IN_HERE.
Qed.
