Require Import P06.

Check optimize_1div_sound: forall a, aeval (optimize_1div a) = aeval a.
