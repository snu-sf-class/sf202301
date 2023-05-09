Require Import P01.

Check ev_sum_not : forall n m, ev (n + m) -> not (ev n) -> not (ev m).
