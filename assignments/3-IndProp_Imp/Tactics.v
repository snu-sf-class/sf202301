
Ltac basic_done :=
  solve [trivial | apply sym_equal; trivial | discriminate | contradiction].

Ltac done :=
  unfold not in *; trivial; hnf; intros;
  solve [try basic_done; split;
         try basic_done; split;
         try basic_done; split;
         try basic_done; split;
         try basic_done; split; basic_done
        | match goal with H : _ -> False |- _ => solve [case H; trivial] end].

Ltac complaining_inj f H :=
  let X := fresh in
  (match goal with | [|- ?P ] => set (X := P) end);
  injection H;
  (lazymatch goal with | [ |- f _ = f _ -> _] => fail | _ => idtac end);
  clear H; intros;
  subst X;
  try subst.

Ltac _clarify :=
  try subst;
  repeat match goal with
    | [H: ?f _             = ?f _             |- _] => complaining_inj f H
    | [H: ?f _ _           = ?f _ _           |- _] => complaining_inj f H
    | [H: ?f _ _ _         = ?f _ _ _         |- _] => complaining_inj f H
    | [H: ?f _ _ _ _       = ?f _ _ _ _       |- _] => complaining_inj f H
    | [H: ?f _ _ _ _ _     = ?f _ _ _ _ _     |- _] => complaining_inj f H
    | [H: ?f _ _ _ _ _ _   = ?f _ _ _ _ _ _   |- _] => complaining_inj f H
    | [H: ?f _ _ _ _ _ _ _ = ?f _ _ _ _ _ _ _ |- _] => complaining_inj f H
    end; try done.

(* auto solver with equality with constructor *)
Ltac clarify :=
  _clarify;
  repeat match goal with
    | H1: ?x = Some _, H2: ?x = None   |- _ => rewrite H2 in H1; _clarify
    | H1: ?x = Some _, H2: ?x = Some _ |- _ => rewrite H2 in H1; _clarify
    end.

(* inversion with subst *)
Ltac inv H := inversion H; clear H; subst.

(* intros with simpl *)
Ltac ins := simpl in *; try done; intros.

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

(* destruct all cases *)
Ltac des_ifs :=
  clarify;
  repeat
    match goal with
    | |- context[match ?x with _ => _ end] =>
        match (type of x) with
        | { _ } + { _ } => destruct x; clarify
        | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; clarify
        end
    | H: context[ match ?x with _ => _ end ] |- _ =>
        match (type of x) with
        | { _ } + { _ } => destruct x; clarify
        | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; clarify
        end
    end.

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

Require Import D.
Import Imp.

Ltac uo := unfold o_bind, o_map, o_join in *.

(* this is an example of automated proof using showed tactics *)
Theorem aeval_iff_aevalR : forall a n,
  (aevalR a n) <-> aeval a = Some n.
Proof with nia || eauto using aevalR.
  split; ins.
  - (* -> *)
    induction H; ins; uo; des_ifs. apply Nat.ltb_ge in Heq...
  - (* <- *)
    gen n.
    induction a; ins; uo; des_ifs; constructor...
    apply Nat.ltb_lt in Heq...
Qed.
