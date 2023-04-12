Require Import P09.

Check trim_head_last : forall A (xs : list A), 2 <=? length xs = true -> exists x ys y, xs = [x] ++ ys ++ [y].
