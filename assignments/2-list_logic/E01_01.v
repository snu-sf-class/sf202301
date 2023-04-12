Require Import P01.

Example test_alternate1: alternate [5] [2;1;5;4;1] = [5;2;1;5;4;1].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [7;8;0] [2;1;4;1] = [7;2;8;1;0;4;1].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1;8;9;90;4;7] [2;1;4;5;1;4] = [1;2;8;1;9;4;90;5;4;1;7;4].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [5;7;9;2;6] [2;1;5] = [5;2;7;1;9;5;2;6].
Proof. reflexivity. Qed.
