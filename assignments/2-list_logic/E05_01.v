Require Import P05.


Check firstn_exact : forall A n (xs ys : list A), n = length xs -> firstn n (xs ++ ys) = xs.
