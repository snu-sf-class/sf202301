Require Export P03.
Export Regexp.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold_left (app (A := _)) ss [] =~ Star re.
Proof.
  exact FILL_IN_HERE.
Qed.
