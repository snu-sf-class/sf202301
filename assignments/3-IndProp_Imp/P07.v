Require Export P06.

(** [20 point in total] Write a relation [bevalR] in the same style as
   [aevalR], and prove that it is equivalent to [beval]. *)

(** Don't use aeval and beval when define bevalR (only use aevalR). *)

(** [10 point] Implement bevalR *)
Inductive bevalR: bexp -> bool -> Prop :=
  (* FILL_IN_HERE *) .

(** Your implementation is checked with examples **)
(** following block should be uncommented before evaluation **)
(** If your definition can't proof these examples using "do 20 try econstructor", **)
(** comment out and write your proofs in following area. **)

(* Lemma rw A B (x : A) (z : B) w P : P x z -> z = w -> P x w. *)
(* Proof. intros. subst. auto. Qed. *)

(* Ltac econs2 := eapply rw; [econstructor|]. *)

(* Example my_bevalR1: bevalR (BNot BTrue) false. *)
(* Proof. do 20 econs2; reflexivity. Qed. *)
(* Example my_bevalR2: bevalR (BEq (APlus (ANum 2) (ANum 1)) (ANum 3)) true. *)
(* Proof. do 20 econs2; reflexivity. Qed. *)
(* Example my_bevalR3: bevalR (BAnd (BLe (AMult (ANum 3) (ANum 1)) *)
(*                                         (AMinus (ANum 1) (ANum 3))) *)
(*                                    BTrue) false. *)
(* Proof. do 20 econs2; reflexivity. Qed. *)


(** [10 point] prove following specification of bevalR *)
(** you should use following theorem to solve last problem *)
Check aeval_iff_aevalR.

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = Some bv.
Proof.
  exact FILL_IN_HERE.
Qed.
