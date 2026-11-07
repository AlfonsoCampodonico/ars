---- MODULE MC ----
EXTENDS AccountableSaga
\* Step 2 depends on step 1; step 3 runs in parallel with both.
\* If step 3 aborts after 1 and 2 committed, 2 must be undone before 1.
MCDeps   == <<{}, {1}, {}>>
MCOwner  == <<"a", "b", "c">>
MCBenef  == <<"c", "a", "b">>
MCOracle == {1}
====
