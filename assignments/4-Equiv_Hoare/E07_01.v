Require Export P07.

Check if_minus_plus :
  {{True}}
  if (X <= Y)
    then (Z := Y - X)
    else (Y := X + Z)
  end
  {{ Y = X + Z}}. 
