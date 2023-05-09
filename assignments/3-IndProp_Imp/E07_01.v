Require Import P07.

Example test_bevalR1: bevalR (BNot BTrue) false.
Proof. try ( solve [do 20 econs2; reflexivity] ); try apply my_bevalR1. Qed.
Example test_bevalR2: bevalR (BEq (APlus (ANum 2) (ANum 1)) (ANum 3)) true.
Proof. try ( solve [do 20 econs2; reflexivity] ); try apply my_bevalR2. Qed.
Example test_bevalR3: bevalR (BAnd (BLe (AMult (ANum 3) (ANum 1))
                                        (AMinus (ANum 1) (ANum 3)))
                                   BTrue) false.
Proof. try ( solve [do 20 econs2; reflexivity] ); try apply my_bevalR3. Qed.
