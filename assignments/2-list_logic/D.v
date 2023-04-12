Require Export Coq.Init.Nat.
Definition FILL_IN_HERE {T: Type} : T.  Admitted.

Inductive option (X:Type) : Type :=
| None
| Some (x : X).

Arguments None {X}.
Arguments Some {X} _.

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


Definition natlist := list nat.

Fixpoint nth_error {X: Type} (l:list X) (n:nat) : option X :=
  match n, l with
  | O, x :: _ => Some x
  | S n, _ :: l => nth_error l n
  | _, _ => None
  end.

Fixpoint length {X: Type} (l:list X) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end.

Definition tl {X: Type} (l:list X) : list X :=
  match l with
  | [] => []
  | _ :: l' => l'
  end.

Fixpoint removelast {X: Type} (l:list X) : list X :=
  match l with
  | [] => []
  | [x] => []
  | x' :: l' => x' :: removelast l'
  end.

Fixpoint firstn {X: Type} (n: nat) (l:list X) : list X :=
  match n, l with
  | 0, _ => []
  | _, [] => []
  | S n', x :: l' => x :: firstn n' l'
  end.

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | nil => nil
  | cons h t => cons (f h) (map f t)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Fixpoint fold_left {X Y: Type} (f: X -> Y -> X) (l: list Y) (i: X) :=
  match l with
  | nil => i
  | x' :: l' => fold_left f l' (f i x')
  end.
