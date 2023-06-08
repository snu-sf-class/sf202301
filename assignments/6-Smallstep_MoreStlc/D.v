Require Export Maps.
Require Export Tactics.

Definition FILL_IN_HERE {T} : T. Admitted.

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat  : ty
  | Ty_Sum  : ty -> ty -> ty
  | Ty_List : ty -> ty
  | Ty_Unit : ty
  | Ty_Prod : ty -> ty -> ty.

Inductive tm : Type :=
  (* pure STLC *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* numbers *)
  | tm_const: nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm
  (* sums *)
  | tm_inl : ty -> tm -> tm
  | tm_inr : ty -> tm -> tm
  | tm_case : tm -> string -> tm -> string -> tm -> tm
          (* i.e., [case t0 of inl x1 => t1 | inr x2 => t2] *)
  (* lists *)
  | tm_nil : ty -> tm
  | tm_cons : tm -> tm -> tm
  | tm_lcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., [case t1 of | nil => t2 | x::y => t3] *)
  (* unit *)
  | tm_unit : tm

  (* You are going to be working on the following extensions: *)

  (* pairs *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
  (* let *)
  | tm_let : string -> tm -> tm -> tm
         (* i.e., [let x = t1 in t2] *)
  (* fix *)
  | tm_fix  : tm -> tm.

(** Note that, for brevity, we've omitted booleans and instead
    provided a single [if0] form combining a zero test and a
    conditional.  That is, instead of writing

       if x = 0 then ... else ...

    we'll write this:

       if0 x then ... else ...
*)

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Declare Custom Entry stlc.
Declare Custom Entry stlc_ty.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "{ x }" := x (in custom stlc at level 1, x constr).

Notation "'Nat'" := Ty_Nat (in custom stlc_ty at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "x * y" := (tm_mult x y) (in custom stlc at level 1,
                                      left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Coercion tm_const : nat >-> tm.

Notation "S + T" :=
  (Ty_Sum S T) (in custom stlc_ty at level 3, left associativity).
Notation "'inl' T t" := (tm_inl T t) (in custom stlc at level 0,
                                         T custom stlc_ty at level 0,
                                         t custom stlc at level 0).
Notation "'inr' T t" := (tm_inr T t) (in custom stlc at level 0,
                                         T custom stlc_ty at level 0,
                                         t custom stlc at level 0).
Notation "'case' t0 'of' '|' 'inl' x1 '=>' t1 '|' 'inr' x2 '=>' t2" :=
  (tm_case t0 x1 t1 x2 t2) (in custom stlc at level 89,
                               t0 custom stlc at level 99,
                               x1 custom stlc at level 99,
                               t1 custom stlc at level 99,
                               x2 custom stlc at level 99,
                               t2 custom stlc at level 99,
                               left associativity).

Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc_ty at level 2, X custom stlc_ty, Y custom stlc_ty at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 0).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 0).

Notation "'List' T" :=
  (Ty_List T) (in custom stlc_ty at level 4).
Notation "'nil' T" := (tm_nil T) (in custom stlc at level 0, T custom stlc_ty at level 0).
Notation "h '::' t" := (tm_cons h t) (in custom stlc at level 2, right associativity).
Notation "'case' t1 'of' '|' 'nil' '=>' t2 '|' x '::' y '=>' t3" :=
  (tm_lcase t1 t2 x y t3) (in custom stlc at level 89,
                              t1 custom stlc at level 99,
                              t2 custom stlc at level 99,
                              x constr at level 1,
                              y constr at level 1,
                              t3 custom stlc at level 99,
                              left associativity).

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc_ty at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).

Notation "'let' x '=' t1 'in' t2" :=
  (tm_let x t1 t2) (in custom stlc at level 0).

Notation "'fix' t" := (tm_fix t) (in custom stlc at level 0).

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{succ t1}> =>
      <{succ [x := s] t1}>
  | <{pred t1}> =>
      <{pred [x := s] t1}>
  | <{t1 * t2}> =>
      <{ ([x := s] t1) * ([x := s] t2)}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 [x := s] t1 then [x := s] t2 else [x := s] t3}>
  (* sums *)
  | <{inl T2 t1}> =>
      <{inl T2 ( [x:=s] t1) }>
  | <{inr T1 t2}> =>
      <{inr T1 ( [x:=s] t2) }>
  | <{case t0 of | inl y1 => t1 | inr y2 => t2}> =>
      <{case ([x:=s] t0) of
         | inl y1 => { if String.eqb x y1 then t1 else <{ [x:=s] t1 }> }
         | inr y2 => {if String.eqb x y2 then t2 else <{ [x:=s] t2 }> } }>
  (* lists *)
  | <{nil _}> =>
      t
  | <{t1 :: t2}> =>
      <{ ([x:=s] t1) :: [x:=s] t2 }>
  | <{case t1 of | nil => t2 | y1 :: y2 => t3}> =>
      <{case ( [x:=s] t1 ) of
        | nil => [x:=s] t2
        | y1 :: y2 =>
        {if String.eqb x y1 then
           t3
         else if String.eqb x y2 then t3
              else <{ [x:=s] t3 }> } }>
  (* unit *)
  | <{unit}> => <{unit}>

  (* pairs *)
  | <{(t1, t2)}> =>
      <{ ([x:=s] t1, [x:=s] t2) }>
  | <{t.fst}> => <{([x:=s] t).fst}>
  | <{t.snd}> => <{([x:=s] t).snd}>
  (* let *)
  | <{let y = t1 in t2}> => 
      if String.eqb x y then <{ let y = [x:=s] t1 in t2 }>
      else <{ let y = [x:=s] t1 in [x:=s] t2 }>
  (* fix *)
  | <{fix t}> => <{fix [x:=s] t}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ----------------------------------------------------------------- *)
(** *** Reduction *)

(** Next we define the values of our language. *)

Inductive value : tm -> Prop :=
  (* In pure STLC, function abstractions are values: *)
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  (* Numbers are values: *)
  | v_nat : forall n : nat,
      value <{n}>
  (* A tagged value is a value:  *)
  | v_inl : forall v T1,
      value v ->
      value <{inl T1 v}>
  | v_inr : forall v T1,
      value v ->
      value <{inr T1 v}>
  (* A list is a value iff its head and tail are values: *)
  | v_lnil : forall T1, value <{nil T1}>
  | v_lcons : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{v1 :: v2}>
  (* A unit is always a value *)
  | v_unit : value <{unit}>
  (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{(v1, v2)}>.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

(** **** Exercise: 3 stars, standard (STLCExtended.step) *)
Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  (* numbers *)
  | ST_Succ : forall t1 t1',
         t1 --> t1' ->
         <{succ t1}> --> <{succ t1'}>
  | ST_SuccNat : forall n : nat,
         <{succ n}> --> <{ {S n} }>
  | ST_Pred : forall t1 t1',
         t1 --> t1' ->
         <{pred t1}> --> <{pred t1'}>
  | ST_PredNat : forall n:nat,
         <{pred n}> --> <{ {n - 1} }>
  | ST_Mulconsts : forall n1 n2 : nat,
         <{n1 * n2}> --> <{ {n1 * n2} }>
  | ST_Mult1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 * t2}> --> <{t1' * t2}>
  | ST_Mult2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 * t2}> --> <{v1 * t2'}>
  | ST_If0 : forall t1 t1' t2 t3,
         t1 --> t1' ->
         <{if0 t1 then t2 else t3}> --> <{if0 t1' then t2 else t3}>
  | ST_If0_Zero : forall t2 t3,
         <{if0 0 then t2 else t3}> --> t2
  | ST_If0_Nonzero : forall n t2 t3,
         <{if0 {S n} then t2 else t3}> --> t3
  (* sums *)
  | ST_Inl : forall t1 t1' T2,
        t1 --> t1' ->
        <{inl T2 t1}> --> <{inl T2 t1'}>
  | ST_Inr : forall t2 t2' T1,
        t2 --> t2' ->
        <{inr T1 t2}> --> <{inr T1 t2'}>
  | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 --> t0' ->
        <{case t0 of | inl x1 => t1 | inr x2 => t2}> -->
        <{case t0' of | inl x1 => t1 | inr x2 => t2}>
  | ST_CaseInl : forall v0 x1 t1 x2 t2 T2,
        value v0 ->
        <{case inl T2 v0 of | inl x1 => t1 | inr x2 => t2}> --> <{ [x1:=v0]t1 }>
  | ST_CaseInr : forall v0 x1 t1 x2 t2 T1,
        value v0 ->
        <{case inr T1 v0 of | inl x1 => t1 | inr x2 => t2}> --> <{ [x2:=v0]t2 }>
  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       <{t1 :: t2}> --> <{t1' :: t2}>
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       <{v1 :: t2}> --> <{v1 :: t2'}>
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 --> t1' ->
       <{case t1 of | nil => t2 | x1 :: x2 => t3}> -->
       <{case t1' of | nil => t2 | x1 :: x2 => t3}>
  | ST_LcaseNil : forall T1 t2 x1 x2 t3,
       <{case nil T1 of | nil => t2 | x1 :: x2 => t3}> --> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1 ->
       value vl ->
       <{case v1 :: vl of | nil => t2 | x1 :: x2 => t3}>
         -->  <{ [x2 := vl] ([x1 := v1] t3) }>
  (* pairs *)
  | ST_Pair1 : forall t1 t1' t2,
       t1 --> t1' ->
       <{(t1, t2)}> --> <{(t1', t2)}>
  | ST_Pair2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       <{(v1, t2)}> --> <{(v1, t2')}>
  | ST_Fst1 : forall t t',
       t --> t' ->
       <{t.fst}> -->
       <{t'.fst}>
  | ST_FstPair : forall v1 v2,
       value v1 ->
       value v2 ->
       <{(v1, v2).fst}> --> <{v1}>
  | ST_Snd1 : forall t t',
       t --> t' ->
       <{t.snd}> -->
       <{t'.snd}>
  | ST_SndPair : forall v1 v2,
       value v1 ->
       value v2 ->
       <{(v1, v2).snd}> --> <{v2}>
  (* let *)
  | ST_Let1 : forall x t1 t1' t2,
       t1 --> t1' ->
       <{let x = t1 in t2}> --> <{let x = t1' in t2}>
  | ST_LetValue: forall x v1 t2,
       value v1 -> 
       <{let x = v1 in t2}> --> <{[x:=v1] t2}>
  (* fix *)
  | ST_Fix1: forall t t',
       t --> t' ->
       <{fix t}> -->
       <{fix t'}>
  | ST_FixAbs: forall xf T1 t,
       <{fix (\xf: T1, t)}> -->
       <{[xf:= (fix (\xf:T1, t))] t}>

  where "t '-->' t'" := (step t t').


Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

(* ----------------------------------------------------------------- *)
(** *** Typing *)

Definition context := partial_map ty.

(** Next we define the typing rules.  These are nearly direct
    transcriptions of the inference rules shown above. *)

Reserved Notation "Gamma '|--' t '\in' T" (at level 40, t custom stlc, T custom stlc_ty at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* pure STLC *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
    (x |-> T2 ; Gamma) |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  (* numbers *)
  | T_Nat : forall Gamma (n : nat),
      Gamma |-- n \in Nat
  | T_Succ : forall Gamma t,
      Gamma |-- t \in Nat ->
      Gamma |-- succ t \in Nat
  | T_Pred : forall Gamma t,
      Gamma |-- t \in Nat ->
      Gamma |-- pred t \in Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma |-- t1 \in Nat ->
      Gamma |-- t2 \in Nat ->
      Gamma |-- t1 * t2 \in Nat
  | T_If0 : forall Gamma t1 t2 t3 T0,
      Gamma |-- t1 \in Nat ->
      Gamma |-- t2 \in T0 ->
      Gamma |-- t3 \in T0 ->
      Gamma |-- if0 t1 then t2 else t3 \in T0
  (* sums *)
  | T_Inl : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- (inl T2 t1) \in (T1 + T2)
  | T_Inr : forall Gamma t2 T1 T2,
      Gamma |-- t2 \in T2 ->
      Gamma |-- (inr T1 t2) \in (T1 + T2)
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T3,
      Gamma |-- t0 \in (T1 + T2) ->
      (x1 |-> T1 ; Gamma) |-- t1 \in T3 ->
      (x2 |-> T2 ; Gamma) |-- t2 \in T3 ->
      Gamma |-- (case t0 of | inl x1 => t1 | inr x2 => t2) \in T3
  (* lists *)
  | T_Nil : forall Gamma T1,
      Gamma |-- (nil T1) \in (List T1)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in (List T1) ->
      Gamma |-- (t1 :: t2) \in (List T1)
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      Gamma |-- t1 \in (List T1) ->
      Gamma |-- t2 \in T2 ->
      (x1 |-> T1 ; x2 |-> <{{List T1}}> ; Gamma) |-- t3 \in T2 ->
      Gamma |-- (case t1 of | nil => t2 | x1 :: x2 => t3) \in T2
  (* unit *)
  | T_Unit : forall Gamma,
      Gamma |-- unit \in Unit
  (* pairs *)
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1, t2) \in (T1 * T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.fst \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.snd \in T2
  (* let *)
  | T_Let : forall Gamma x t1 t2 T1 T2,
      Gamma |-- t1 \in T1 ->
      (x |->T1; Gamma) |-- t2 \in T2 ->
      Gamma |-- (let x = t1 in t2) \in T2
  (* fix *)
  | T_Fix : forall Gamma t T1,
      Gamma |-- t \in (T1 -> T1) ->
      Gamma |-- (fix t) \in T1

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.


Definition TF P := P \/ ~ P.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').

Inductive lvalue (T: ty) : tm -> Prop :=
| L_nil : lvalue T (tm_nil T)
| L_cons tl x (LTL: lvalue T tl) (TY: empty |-- x \in T) : lvalue T <{x::tl}>.

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck : core.

Inductive appears_free_in (x : string) : tm -> Prop :=
  | afi_var : appears_free_in x <{x}>
  | afi_app1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{t1 t2}>
  | afi_app2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{t1 t2}>
  | afi_abs : forall y T1 t1,
      y <> x  ->
      appears_free_in x t1 ->
      appears_free_in x <{\y:T1, t1}>
  | afi_if1 : forall t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x <{if0 t1 then t2 else t3}>
  | afi_if2 : forall t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x <{if0 t1 then t2 else t3}>
  | afi_if3 : forall t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x <{if0 t1 then t2 else t3}>
  | afi_succ : forall t,
      appears_free_in x t ->
      appears_free_in x <{succ t}>
  | afi_pred : forall t,
      appears_free_in x t ->
      appears_free_in x <{pred t}>
  | afi_mult1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{t1 * t2}>
  | afi_mult2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{t1 * t2}>
  | afi_inl : forall t T1,
      appears_free_in x t ->
      appears_free_in x <{inl T1 t}>
  | afi_inr : forall t T2,
      appears_free_in x t ->
      appears_free_in x <{inr T2 t}>
  | afi_case1 : forall y1 y2 t0 t1 t2,
      appears_free_in x t0 ->
      appears_free_in x <{case t0 of | inl y1 => t1 | inr y2 => t2}>
  | afi_case2 : forall y1 y2 t0 t1 t2,
      y1 <> x  ->
      appears_free_in x t1 ->
      appears_free_in x <{case t0 of | inl y1 => t1 | inr y2 => t2}>
  | afi_case3 : forall y1 y2 t0 t1 t2,
      y2 <> x  ->
      appears_free_in x t2 ->
      appears_free_in x <{case t0 of | inl y1 => t1 | inr y2 => t2}>
  | afi_cons1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{t1 :: t2}>
  | afi_cons2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{t1 :: t2}>
  | afi_lcase1 : forall y1 y2 t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x <{case t1 of | nil => t2 | y1 :: y2 => t3}>
  | afi_lcase2 : forall y1 y2 t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x <{case t1 of | nil => t2 | y1 :: y2 => t3}>
  | afi_lcase3 : forall y1 y2 t1 t2 t3,
      y1 <> x  ->
      y2 <> x  ->
      appears_free_in x t3 ->
      appears_free_in x <{case t1 of | nil => t2 | y1 :: y2 => t3}>
  | afi_pair1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{(t1, t2)}>
  | afi_pair2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{(t1, t2)}>
  | afi_fst : forall t,
      appears_free_in x t ->
      appears_free_in x <{t.fst}>
  | afi_snd : forall t,
      appears_free_in x t ->
      appears_free_in x <{t.snd}>
  | afi_let1 : forall y t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ let y = t1 in t2 }>
  | afi_let2 : forall y t1 t2,
      y <> x  ->
      appears_free_in x t2 ->
      appears_free_in x <{ let y = t1 in t2 }>
  | afi_fix : forall t,
      appears_free_in x t ->
        appears_free_in x <{fix t}>
  .

Hint Constructors appears_free_in : core.
