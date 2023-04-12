Require Export P09.


Theorem material_implication_implies_de_morgan: 
(forall (P Q:Prop), (P -> Q) -> (not P \/ Q)) -> (forall (P Q: Prop), not (not P /\ not Q) -> P \/ Q).
Proof.
exact FILL_IN_HERE.
Qed.
