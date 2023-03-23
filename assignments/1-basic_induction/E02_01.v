Require Import P02.



Check xorb_to_andb : forall b c : bool,
  xorb b c = true -> andb b c = false.

