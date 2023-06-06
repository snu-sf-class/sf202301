(* inversion with subst *)
Ltac inv H := inversion H; clear H; subst.

Ltac des1 :=
  match goal with
  | H : exists x, ?p |- _ =>
      let x' := fresh x in destruct H as [x' H]
  | H : ?p /\ ?q |- _ =>
      let x' := fresh H in
      let y' := fresh H in
      destruct H as [x' y']
  | H : ?p <-> ?q |- _ =>
      let x' := fresh H in
      let y' := fresh H in
      destruct H as [x' y']
  | H : ?p \/ ?q |- _ =>
      let x' := fresh H in
      let y' := fresh H in
      destruct H as [x' | y']
  end.

(* destruct hypothesises *)
Ltac des := repeat des1.

(* duplicate hypothesises *)
Tactic Notation "dup" hyp(H) :=
  let H' := fresh H in assert (H' := H).

Lemma __mp__: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.

(* exploit *)
Ltac hexploit H := eapply __mp__; [eapply H|].

(* induction with variables *)
Tactic Notation "induction" "[" ident_list(y) "]" ident(x)  :=
  first [ try (intros until x); revert y; induction x
        | red; try (intros until x); revert y; induction x ].

(* dependent destruction *)
Tactic Notation "depdes" ident(_something_which_shold_not_occur_in_the_goal_) :=
  (let _x_ := type of _something_which_shold_not_occur_in_the_goal_
   in dependent destruction _something_which_shold_not_occur_in_the_goal_).
Tactic Notation "depdes" ident(a) ident(b) :=
  (depdes a; depdes b).
Tactic Notation "depdes" ident(a) ident(b) ident(c) :=
  (depdes a; depdes b c).
Tactic Notation "depdes" ident(a) ident(b) ident(c) ident(d) :=
  (depdes a; depdes b c d).

(* generalize dependent *)
Tactic Notation "gen" ident(X1) :=
  generalize dependent X1.
Tactic Notation "gen" ident(X1) ident(X2) :=
  gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) :=
  gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4)  :=
  gen X4; gen X3; gen X2; gen X1.

Tactic Notation "econs" := econstructor.

Ltac on_last_hyp tac :=
  match goal with [ H : _ |- _ ] => first [ tac H | fail 1 ] end.

(* revert until id *)
Ltac revert_until id :=
  on_last_hyp
    ltac:(fun id' =>
            match id' with
            | id => idtac
            | _ => revert id' ; revert_until id
            end).

(* most general induction *)
Ltac ginduction H :=
  move H at top; revert_until H; induction H.

(* construct argument of H *)
Ltac special H :=
  match type of H with
  | ?A -> ?B =>
      let a := fresh in assert (a: A); [|specialize (H a)]
  end.

Ltac ex x := eapply (ex_intro _ (x _)).

Ltac simpl_proj :=
  do 5 (simpl (fst (_, _)) in *; simpl (snd (_, _)) in * ).

(* cleaning equality hypothesises independent to a goal *)
Ltac clean :=
  repeat match goal with
    | H: True |- _
      => clear H
    | H: ?x = ?y |- _
      => try (has_evar x; fail 2); try (has_evar y; fail 2);
        change x with y in H; clear H
    end
  ; simpl_proj.

