From Coq Require Export Bool.Bool.
From Coq Require Export Init.Nat.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
From Coq Require Export Strings.String.
Require Export Maps Tactics.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Default Goal Selector "!".

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

(** Definitions and tools for option monads **)
Definition o_map {A} {B} (oa: option A) (f: A -> B): option B :=
  match oa with
  | Some a => Some (f a)
  | None => None
  end.

Definition o_join {A} (a: option (option A)): option A :=
  match a with
  | Some a => a
  | None => None
  end.

Definition o_bind {A} {B} (oa: option A) (f: A -> option B): option B := o_join (o_map oa f).

Notation "'do' X <- A ; B" := (o_bind A (fun X => B))
                               (at level 200, X ident, A at level 100, B at level 200).

Notation "'guard' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200, only parsing).

(** This unfolds all notations. Use with Tactics.v **)
Ltac uo := unfold o_bind, o_map, o_join in *.




(** Reconstruction of Imp with erroneous state**)

Definition state := option (total_map nat).

Definition update_opt {A : Type} (optm : option (total_map A)) (x : string) (optv : option A) :=
  match optm, optv with
  | Some m, Some v => Some (t_update m x v)
  | _, _ => None
  end.

Definition empty_state : state := Some (t_empty 0).

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "x / y" := (ADiv x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"  := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"  := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

Fixpoint aeval (st : state) (a : aexp) : option nat :=
  match a with
  | ANum n        => do x <- st ; Some n
  | AId x         => do mem <- st ; Some (mem x)
  | <{a1 + a2}>   => do A1 <- (aeval st a1) ; do A2 <- (aeval st a2) ; Some (A1 + A2)
  | <{a1 - a2}>   => do A1 <- (aeval st a1) ; do A2 <- (aeval st a2) ; Some (A1 - A2)
  | <{a1 * a2}>   => do A1 <- (aeval st a1) ; do A2 <- (aeval st a2) ; Some (A1 * A2)
  | <{a1 / a2}>   => do A1 <- (aeval st a1) ; do A2 <- (aeval st a2) ; guard (0 <? A2) ; Some (A1 / A2)
  end.

Fixpoint beval (st : state) (b : bexp) : option bool :=
  match b with
  | <{true}>      => do x <- st ; Some true
  | <{false}>     => do x <- st ; Some false
  | <{a1 = a2}>   => do A1 <- (aeval st a1) ; do A2 <- (aeval st a2) ; Some (A1 =? A2)
  | <{a1 <> a2}>  => do A1 <- (aeval st a1) ; do A2 <- (aeval st a2) ; Some (negb (A1 =? A2))
  | <{a1 <= a2}>  => do A1 <- (aeval st a1) ; do A2 <- (aeval st a2) ; Some (A1 <=? A2)
  | <{a1 > a2}>   => do A1 <- (aeval st a1) ; do A2 <- (aeval st a2) ; Some (negb (A1 <=? A2))
  | <{~ b1}>      => do B  <- (beval st b1) ; Some (negb B)
  | <{b1 && b2}>  => do B1 <- (beval st b1) ; do B2 <- (beval st b2) ; Some (andb B1 B2) 
  end.

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st st' a optn x,
      aeval st a = optn ->
      update_opt st x optn = st' ->
      st =[ x := a ]=> st'
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfErr : forall st b c1 c2,
      beval st b = None ->
      st =[ if b then c1 else c2 end]=> None
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = Some true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = Some false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileErr : forall b st c,
      beval st b = None ->
      st =[ while b do c end ]=> None
  | E_WhileFalse : forall b st c,
      beval st b = Some false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = Some true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

Definition refines (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') -> (st =[ c2 ]=> st').

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp x (ANum n)
  | VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 + a2 }>)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 - a2 }>)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 * a2 }>)
  | VNUDiv : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 / a2 }>).

Fixpoint subst_aexp (i : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId i'       =>
      if string_dec i i' then u else AId i'
  | APlus a1 a2  =>
      APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2  =>
      AMult (subst_aexp i u a1) (subst_aexp i u a2)
  | ADiv a1 a2  =>
      ADiv (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Fixpoint optimize_1div_aexp (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | APlus e1 e2 => APlus (optimize_1div_aexp e1) (optimize_1div_aexp e2)
  | AMinus e1 e2 => AMinus (optimize_1div_aexp e1) (optimize_1div_aexp e2)
  | AMult e1 e2 => AMult (optimize_1div_aexp e1) (optimize_1div_aexp e2)
  | ADiv e1 (ANum 1) => e1
  | ADiv e1 e2 => ADiv (optimize_1div_aexp e1) (optimize_1div_aexp e2)
  end.

Fixpoint optimize_1div_bexp (b:bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse 
  | BEq a1 a2 => BEq (optimize_1div_aexp a1) (optimize_1div_aexp a2)
  | BNeq a1 a2 => BNeq (optimize_1div_aexp a1) (optimize_1div_aexp a2)
  | BLe a1 a2 => BLe (optimize_1div_aexp a1) (optimize_1div_aexp a2)
  | BGt a1 a2 => BGt (optimize_1div_aexp a1) (optimize_1div_aexp a2)
  | BNot b => BNot (optimize_1div_bexp b)
  | BAnd b1 b2 => BAnd (optimize_1div_bexp b1) (optimize_1div_bexp b2)
  end.

Fixpoint optimize_1div_com (c:com) : com :=
  match c with
  | CSkip => CSkip
  | CAsgn x a => CAsgn x (optimize_1div_aexp a)
  | CSeq c1 c2 => CSeq (optimize_1div_com c1) (optimize_1div_com c2)
  | CIf b c1 c2 => CIf (optimize_1div_bexp b) (optimize_1div_com c1) (optimize_1div_com c2)
  | CWhile b c => CWhile (optimize_1div_bexp b) (optimize_1div_com c)
  end.


(* Reconstruction of Hoare.v with erroneous state *)

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition Aexp : Type := state -> option nat.

Definition assert_of_Prop (P : Prop) : Assertion :=
  fun st => 
    match st with 
    | Some _ => P 
    | _ => False 
    end.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => Some n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.
Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.
Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).
Definition lift_rel {A : Type} (R : A -> A -> Prop) : option A -> option A -> Prop := 
  fun opta1 opta2 =>
    match opta1, opta2 with
    | Some a1, Some a2 => R a1 a2
    | _, _ => False
    end
.

Definition lift_op {A : Type} (F : A -> A -> A) : option A -> option A -> option A := 
  fun opta1 opta2 =>
    match opta1, opta2 with
    | Some a1, Some a2 => Some (F a1 a2)
    | _, _ => None
    end
.

Definition opt_div a b := 
  match b with 
  | Some (S b') => Some (div a (S b'))
  | _ => None 
  end.

Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st ->  assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <->  assert Q st) : assertion_scope.
Notation "a = b" := (fun st => lift_rel (@eq nat) (mkAexp a st) (mkAexp b st)) : assertion_scope.
Notation "a <> b" := (fun st => lift_rel (fun n1 n2 : nat => eq n1 n2 -> False) (mkAexp a st) (mkAexp b st)) : assertion_scope.
Notation "a <= b" := (fun st => lift_rel le (mkAexp a st) (mkAexp b st)) : assertion_scope.
Notation "a < b" := (fun st => lift_rel lt (mkAexp a st) (mkAexp b st)) : assertion_scope.
Notation "a >= b" := (fun st => lift_rel ge (mkAexp a st) (mkAexp b st)) : assertion_scope.
Notation "a > b" := (fun st => lift_rel gt (mkAexp a st) (mkAexp b st)) : assertion_scope.
Notation "a + b" := (fun st => lift_op add (mkAexp a st) (mkAexp b st)) : assertion_scope.
Notation "a - b" := (fun st => lift_op sub (mkAexp a st) (mkAexp b st)) : assertion_scope.
Notation "a * b" := (fun st => lift_op mult (mkAexp a st) (mkAexp b st)) : assertion_scope.

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st'  ->
     P st  ->
     Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

  Definition assn_sub X a (P:Assertion) : Assertion :=
    fun st => P (update_opt st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level, a custom com) : hoare_spec_scope.

Definition bassn b : Assertion :=
  fun st => (beval st b = Some true).

Coercion bassn : bexp >-> Assertion.

Arguments bassn /.

Notation "~ b" := (fun st => beval st b = Some false) : assertion_scope.

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  - (* E_IfErr, b evaluates to None *)
      reflexivity.
  - (* E_IfErr, b evaluates to true *)
      rewrite H in H5. discriminate.
  - (* E_IfErr, b evaluates to false *)
      rewrite H in H5. discriminate.
  - (* E_IfTrue, b evaluates to None (contradiction)*)
      rewrite H in H5. discriminate.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to None (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileErr, b evaluates to None *)
    reflexivity.
  - (* E_WhileErr, b evaluates to true (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileErr, b evaluates to false (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileFalse, b evaluates to None (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to None (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  ins. split; ins; inv H1; econs; try eapply H in H4; try eapply H0 in H7; eauto.
Qed.


Theorem CAsgn_congruence : forall x a a',
  aequiv a a' ->
  cequiv <{x := a}> <{x := a'}>.
Proof.
  intros x a a' Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. eapply E_Asgn;[|eauto]. 
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. eapply E_Asgn;[|eauto].
    rewrite Heqv. reflexivity.  Qed.

Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof.
  (* WORKED IN CLASS *)

  (* We will prove one direction in an "assert"
     in order to reuse it for the converse. *)
  assert (A: forall (b b' : bexp) (c c' : com) (st st' : state),
             bequiv b b' -> cequiv c c' ->
             st =[ while b do c end ]=> st' ->
             st =[ while b' do c' end ]=> st').
  { unfold bequiv,cequiv.
    intros b b' c c' st st' Hbe Hc1e Hce.
    remember <{ while b do c end }> as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + econstructor. rewrite Hbe in H. auto.
    + (* E_WhileFalse *)
      eapply E_WhileFalse. rewrite <- Hbe. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* show loop runs *) rewrite <- Hbe. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity. }

  intros. split.
  - apply A; assumption.
  - apply A.
    + unfold bequiv. intros. rewrite H. auto.
    + unfold cequiv in *. intros. rewrite H0. split; eauto.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  unfold hoare_triple.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  eauto.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P Q Q' c Hhoare Himp st st' Heval Hpre.
  apply Himp.
  apply Hhoare with (st := st).
  - assumption.
  - assumption.
Qed.


Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.


Ltac assn_auto :=
  repeat (simpl; unfold "->>", assn_sub, t_update, bassn; uo);
  intros [m|] H; inversion H;
  repeat (simpl; unfold "->>", assn_sub, t_update, bassn; uo);
  repeat split; intros; clarify;
  try rewrite <- Nat.eqb_eq in *;
  try rewrite <- Nat.leb_le in *;  (* for inequalities *)
  auto; try lia.