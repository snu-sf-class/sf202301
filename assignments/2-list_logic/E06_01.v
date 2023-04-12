Require Import P06.

Check rev_removelast_rev_tl : forall l : natlist, rev (removelast (rev l)) = tl l.
