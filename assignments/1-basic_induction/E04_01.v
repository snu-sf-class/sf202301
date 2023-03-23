Require Import P04.



Check xorb_eq_andb:
  forall (b c : bool),
  (xorb b c = andb b c) ->
  b = c.

