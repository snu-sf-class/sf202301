From Coq Require Export Bool.Bool.
From Coq Require Export Init.Nat.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
From Coq Require Export Strings.String.
Require Export HoareDiv.
Require Export Tactics.
Import Nat.

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

Theorem hoare_if_wp : forall P1 P2 Q (b:bexp) c1 c2,
    {{ P1 }} c1 {{ Q }} ->
    {{ P2 }} c2 {{ Q }} ->
    {{ (b -> P1) /\ (~ b -> P2) }} if b then c1 else c2 end {{ Q }}.
Proof.
  intros P1 P2 Q b c1 c2 HTrue HFalse st st' HE [HP1 HP2].
  inversion HE; subst; eauto.
Qed.

(* ================================================================= *)
(** ** Div *)

Theorem hoare_div : forall Q (X Y Z: string),
  {{ (fun st => st Z <> 0 /\ (st Y = (st Y / st Z) * st Z + (st Y mod st Z) -> (st Y mod st Z) < st Z -> Q[X |-> ANum (st Y / st Z)] st)) }} X := Y / Z {{Q}}.
Proof.
  unfold hoare_triple. intros.
  destruct H0 as [? ?].
  inversion H; subst; try nia.
  replace n with (st Y / st Z); eauto.
  - eexists. split; eauto.
    apply H1.
    + rewrite (div_mod_eq (st Y) (st Z)) at 1. nia.
    + eauto using mod_upper_bound.
  - symmetry.
    apply (div_unique (st Y) (st Z) n (st Y - n * st Z)); nia.
Qed.

Hint Resolve hoare_div : hoare.


Lemma assert_implies_refl (P: Assertion):
  P ->> P.
Proof.
  red; intros. eauto.
Qed.

Ltac hauto_vc :=
  eauto;
  unfold "->>", assn_sub, t_update, bassn, ap, ap2;
  intros; simpl in *;
  repeat
    match goal with
    | [H: _ <> true |- _] => apply not_true_iff_false in H
    | [H: _ <> false |- _] => apply not_false_iff_true in H
    | [H: _ /\ _ |- _] => destruct H
    | [H: _ && _ = true |- _] => apply andb_true_iff in H
    | [H: _ && _ = false |- _] => apply andb_false_iff in H
    | [H: _ || _ = true |- _] => apply orb_true_iff in H
    | [H: _ || _ = false |- _] => apply orb_false_iff in H
    | [H: negb _ = true |- _] => eapply negb_true_iff in H
    | [H: negb _ = false |- _] => eapply negb_false_iff in H
    | [H: (_ =? _) = true |- _] => eapply beq_nat_true in H
    | [H: (_ =? _) = false |- _] => eapply beq_nat_false in H
    end;
  repeat (
    try rewrite -> eqb_eq in *;
    try rewrite -> leb_le in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *
  );
  try discriminate; try contradiction; eauto; subst; try nia;
  repeat (split; intros; [eauto; nia|]);
  intros.

Ltac hauto_split1 :=
  try match goal with
      | [|- {{_}} skip {{_}}] =>
        first [eapply hoare_skip; fail | eapply hoare_consequence_pre; [eapply hoare_skip|]]
      | [|- {{_}} _ := _ {{_}}] =>
        first [eapply hoare_asgn;[] | eapply hoare_consequence_pre; [eapply hoare_asgn|]]
      | [|- {{_}} _ := _ / _ {{_}}] =>
        first [eapply hoare_div;[] | eapply hoare_consequence_pre; [eapply hoare_div|]]
      | [|- {{_}} _; _ {{_}}] =>
        eapply hoare_seq
      | [|- {{_}} if _ then _ else _ end {{_}}] =>
        first [eapply hoare_if_wp;[|] | eapply hoare_consequence_pre; [eapply hoare_if_wp|]]
      end.

Ltac hauto :=
  intros;
  match goal with
  | [|- {{_}} _ {{_}}] => repeat hauto_split1
  | _ => idtac
  end;
  try (intros; apply assert_implies_refl);
  try (hauto_vc; fail);
  try (exact (t_empty 0)).

Ltac hauto_while P :=
  intros;
  first[
      eapply (hoare_while P) |
      eapply hoare_consequence_post; [eapply (hoare_while P)|] |
      eapply hoare_consequence_post; [eapply hoare_consequence_pre; [eapply (hoare_while P)|]|]
    ];
  hauto.

Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', s =[ c ]=> s' -> exists s'', s' = Some s'' /\ Q s''. 