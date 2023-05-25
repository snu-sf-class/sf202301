Require Export P01.

Lemma check_multiple_correct: forall (m q r: nat),
  {{ X = q*m + r /\ Y = m /\ r < m /\ m > 0 }}
    Z := X / Y;
    if X = Z*Y
    then Z := 1
    else Z := 0
    end
  {{ (r = 0 /\ Z = 1) \/ (r <> 0 /\ Z = 0) }}.
Proof.
  exact FILL_IN_HERE.
Qed.