Require Import P07.

Check beval_iff_bevalR : forall b bv, bevalR b bv <-> beval b = Some bv.
