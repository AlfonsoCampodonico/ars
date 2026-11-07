---- MODULE MCOracleByzOwner ----
EXTENDS AccountableSaga
\* Steps 1 and 2 run in parallel; step 3 waits for both.
\* Step 1: honest a -> Byzantine c, settled by an oracle.
\* Step 2: Byzantine c -> honest b, no oracle (disputes possible).
\* Step 3: honest b -> honest a.
MCDeps   == <<{}, {}, {1, 2}>>
MCOwner  == <<"a", "c", "b">>
MCBenef  == <<"c", "b", "a">>
\* Same saga, but the oracle covers step 2, where the Byzantine org is OWNER.
MCOracle == {2}
====
