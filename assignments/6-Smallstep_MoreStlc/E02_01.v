Require Export P02.

Check canonical_forms_list : forall t T, empty |-- t \in (List T) -> value t -> lvalue T t.