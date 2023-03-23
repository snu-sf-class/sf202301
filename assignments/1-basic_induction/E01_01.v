Require Import P01.



Example test_greater_triple1:             (greater_triple 0 0) = false.
Proof. reflexivity. Qed.
Example test_greater_triple2:             (greater_triple 1 3) = false.
Proof. reflexivity. Qed.
Example test_greater_triple3:             (greater_triple 12 37) = true.
Proof. reflexivity. Qed.
