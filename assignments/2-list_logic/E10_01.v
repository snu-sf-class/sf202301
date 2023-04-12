Require Import P10.


Check material_implication_implies_de_morgan: 
(forall (P Q:Prop), (P -> Q) -> (not P \/ Q)) -> (forall (P Q: Prop), not (not P /\ not Q) -> P \/ Q).
