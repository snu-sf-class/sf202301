Require Export P03.

Theorem unique_types : forall Gamma e T T',
  Gamma |-- e \in T ->
  Gamma |-- e \in T' ->
  T = T'.
Proof.
    exact FILL_IN_HERE.
Qed.