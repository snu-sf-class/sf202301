Require Export P03.

Check aeval_sub : forall x st a,
  var_not_used_in_aexp x a ->
  aeval (update_opt st x (aeval st a)) a = aeval st a.
