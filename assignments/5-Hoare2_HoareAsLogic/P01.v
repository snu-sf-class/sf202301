Require Export D.

Definition two_loops_dec : forall a b c : nat,
    {{ True }}
      X := 0;
      Y := 0;
      Z := a;
      while Y <> b do
        X := X + Z; 
        Y := Y + 1
      end;
      Z := X;
      X := 0;
      Y := 0;
      while Y <> c do
        X := X + Z;
        Y := Y + 1
      end
    {{ X = a * b * c }}.
Proof.
  exact FILL_IN_HERE.
Qed.