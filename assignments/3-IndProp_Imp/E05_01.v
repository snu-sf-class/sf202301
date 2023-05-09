Require Import P05.

Check empty_is_empty : forall T (s : list T), not (s =~ EmptySet).
