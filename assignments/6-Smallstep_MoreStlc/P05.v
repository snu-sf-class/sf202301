Require Export P04.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |-- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |-- t \in T.
Proof.
    exact FILL_IN_HERE.
Qed.