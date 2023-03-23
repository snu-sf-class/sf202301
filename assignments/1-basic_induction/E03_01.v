Require Import P03.



Check xorb_fn_applied_twice :
  forall (f : bool -> bool) (y : bool),
  (forall (x : bool), f x = xorb y x) ->
  forall (b : bool), f (f b) = b.

