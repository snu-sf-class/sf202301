Require Export P03.

Theorem not_hoare_asgn_fwd :
  ~ (forall m a P,
      {{fun st => P st /\ aeval st X = m}}
        X := a
      {{fun st => P (update_opt st X m)
            /\ aeval st X = aeval (update_opt st X m) a }}).
Proof.
  exact FILL_IN_HERE.
Qed.