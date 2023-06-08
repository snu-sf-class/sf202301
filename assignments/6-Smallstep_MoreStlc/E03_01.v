Require Export P03.

Check unique_types : forall Gamma e T T',
  Gamma |-- e \in T ->
  Gamma |-- e \in T' ->
  T = T'.