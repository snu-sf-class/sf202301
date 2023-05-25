Require Export P03.

Theorem hoare_asgn_is_general : forall Q a, 
    wp <{X := a}> Q <<->> Q [X |-> a].
Proof.
  exact FILL_IN_HERE.
Qed.

