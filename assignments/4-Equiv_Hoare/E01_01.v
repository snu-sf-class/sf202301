Require Export P01.

Check loop_never_stops : forall st st',
  ~ ( Some st =[ Y := 0; while X <= Y do X := X - Y end ]=> st').
