Require Export P04.

Check hoare_asgn_is_general : forall Q a, 
    wp <{X := a}> Q <<->> Q [X |-> a].

