Require Export D.

Theorem loop_never_stops : forall st st',
  ~ ( Some st =[ Y := 0; while X <= Y do X := X - Y end ]=> st').
Proof.
  exact FILL_IN_HERE.
Qed.