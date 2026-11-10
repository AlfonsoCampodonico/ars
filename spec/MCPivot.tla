---- MODULE MCPivot ----
EXTENDS AccountableSaga
\* Steps 1 and 2 run in parallel; step 3 waits for both and is a PIVOT
\* (its effect can't be undone). Honest b performs it for Byzantine c, so c
\* can dispute it (hold) or ignore it (abort with the effect done).
MCDeps   == <<{}, {}, {1, 2}>>
MCOwner  == <<"a", "c", "b">>
MCBenef  == <<"c", "b", "c">>
MCOracle == {1}
MCPivot  == {3}
OneClaim == Cardinality(claims) <= 1
====
