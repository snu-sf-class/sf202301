Require Export P03.

Check log_correct_solution: forall (n m: nat), n > 1 -> m > 0 ->
  {{ X = n /\ Y = m }}
    Z := 0;
    while (Y <= X) do
      Z := Z + 1;    
      X := X / Y
    end
  {{ ap2 pow m Z <= n /\ n < ap2 pow m (1+Z) }}.