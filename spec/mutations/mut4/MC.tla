---- MODULE MC ----
EXTENDS AccountableSaga
\* Diamond whose last step is a pivot that honest b performs for Byzantine c.
\* If c never answers, the step aborts and b can't take the effect back.
MCDeps   == <<{}, {}, {1, 2}>>
MCOwner  == <<"a", "c", "b">>
MCBenef  == <<"c", "b", "c">>
MCOracle == {1}
MCPivot  == {3}
OneClaim == Cardinality(claims) <= 1
====
