Require Export P06.

Theorem if_minus_plus :
  {{True}}
  if (X <= Y)
    then (Z := Y - X)
    else (Y := X + Z)
  end
  {{ Y = X + Z}}. 
Proof.
  exact FILL_IN_HERE.
Qed.
