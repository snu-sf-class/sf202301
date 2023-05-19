Require Export P08.

(* Make your own hoare rule and use in your proof *)
Check div_spec: forall (a b : nat),
  {{ True }}
   <{ X := a;
      Y := 0;
      while b <= X do
        X := X - b;
        Y := Y + 1
      end }>
  {{ Y = a / b }}.
