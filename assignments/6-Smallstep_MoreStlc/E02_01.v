Require Export P02.

Check distributive_law : exists (f: tm -> tm), forall Gamma S T1 T2, 
(forall t : tm,
Gamma |-- t \in ((S * T1) + (S * T2)) ->
let t' := f t in Gamma |-- t' \in (S * (T1 + T2)) ) /\
(forall t1 t2, 
Gamma |-- t1 \in ((S * T1) + (S * T2)) ->
Gamma |-- t2 \in ((S * T1) + (S * T2)) ->
f t1 = f t2 -> t1 = t2) /\
(forall t2, 
Gamma |-- t2 \in (S * (T1 + T2)) ->
exists t1, 
Gamma |-- t1 \in ((S * T1) + (S * T2)) /\ f t1 = t2).

