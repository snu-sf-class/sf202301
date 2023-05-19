Require Export P05.

Check hoare_if : forall P1 P2 Q (b:bexp), exists P, forall P' c1 c2,
  {{ P1 }} c1 {{Q}} ->
  {{ P2 }} c2 {{Q}} ->
  {{ P' }} if b then c1 else c2 end {{Q}} ->
  (P' ->> P).
