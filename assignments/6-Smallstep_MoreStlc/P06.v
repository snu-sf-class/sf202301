Require Export P05.

Theorem soundness : forall t t' T,
  empty |-- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
    exact FILL_IN_HERE.
Qed.