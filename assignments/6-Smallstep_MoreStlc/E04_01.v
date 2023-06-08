Require Export P04.

Check context_invariance : forall Gamma Gamma' t T,
     Gamma |-- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |-- t \in T.