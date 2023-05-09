From Coq Require Export Bool.Bool.
From Coq Require Export Init.Nat.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
From Coq Require Export Strings.String.
Export ListNotations.

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

Module Natord.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).

End Natord.


Module Regexp.

Inductive reg_exp (T : Type) : Type :=
| EmptySet
| EmptyStr
| Char (t : T)
| App (r1 r2 : reg_exp T)
| Union (r1 r2 : reg_exp T)
| Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.


Reserved Notation "s =~ re" (at level 80).
Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
| MEmpty : [] =~ EmptyStr
| MChar x : [x] =~ (Char x)
| MApp s1 re1 s2 re2
    (H1 : s1 =~ re1)
    (H2 : s2 =~ re2)
  : (s1 ++ s2) =~ (App re1 re2)
| MUnionL s1 re1 re2
    (H1 : s1 =~ re1)
  : s1 =~ (Union re1 re2)
| MUnionR re1 s2 re2
    (H2 : s2 =~ re2)
  : s2 =~ (Union re1 re2)
| MStar0 re : [] =~ (Star re)
| MStarApp s1 s2 re
    (H1 : s1 =~ re)
    (H2 : s2 =~ (Star re))
  : (s1 ++ s2) =~ (Star re)
               
where "s =~ re" := (exp_match s re).

End Regexp.

Module Omonad.

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

Notation "'assertion' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200, only parsing).


Ltac uo := unfold o_bind, o_map, o_join in *.

End Omonad.

Module Imp.
  Export Omonad.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b1 : bexp)
  | BAnd (b1 b2 : bexp).

Fixpoint aeval (a : aexp) : option nat :=
  match a with
  | ANum n => Some n
  | APlus  a1 a2 => do A1 <- (aeval a1) ; do A2 <- (aeval a2) ; Some (A1 + A2)
  | AMinus a1 a2 => do A1 <- (aeval a1) ; do A2 <- (aeval a2) ; Some (A1 - A2)
  | AMult  a1 a2 => do A1 <- (aeval a1) ; do A2 <- (aeval a2) ; Some (A1 * A2)
  | ADiv   a1 a2 => do A1 <- (aeval a1) ; do A2 <- (aeval a2) ; assertion (0 <? A2) ; Some (A1 / A2)
  end.

Fixpoint beval (b : bexp) : option bool :=
  match b with
  | BTrue       =>  Some true
  | BFalse      =>  Some false
  | BEq a1 a2   =>  do A1 <- (aeval a1) ; do A2 <- (aeval a2) ; Some (A1 =? A2)
  | BLe a1 a2   =>  do A1 <- (aeval a1) ; do A2 <- (aeval a2) ; Some (A1 <=? A2)
  | BNot b1      =>  do B <- (beval b1) ; Some (negb B)
  | BAnd b1 b2  =>  do B1 <- (beval b1) ; do B2 <- (beval b2) ; Some (andb B1 B2) 
  end.

Fixpoint optimize_1div (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus e1 e2 => APlus (optimize_1div e1) (optimize_1div e2)
  | AMinus e1 e2 => AMinus (optimize_1div e1) (optimize_1div e2)
  | AMult e1 e2 => AMult (optimize_1div e1) (optimize_1div e2)
  | ADiv e1 (ANum 1) => e1
  | ADiv e1 e2 => ADiv (optimize_1div e1) (optimize_1div e2)
  end.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2)
  | E_ADiv (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      n2 > 0 ->
      aevalR (ADiv e1 e2) (n1 / n2).


End Imp.

