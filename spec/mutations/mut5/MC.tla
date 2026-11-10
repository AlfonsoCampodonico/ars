---- MODULE MC ----
EXTENDS AccountableSaga
\* Steps 1 and 2 run in parallel; step 3 waits for both.
\* Step 1: honest a -> Byzantine c, settled by an oracle.
\* Step 2: Byzantine c -> honest b, no oracle (disputes possible).
\* Step 3: honest b -> honest a.
MCDeps   == <<{}, {}, {1, 2}>>
MCOwner  == <<"a", "c", "b">>
MCBenef  == <<"c", "b", "a">>
MCOracle == {1}
MCPivot  == {}
\* State constraints for censoring-operator configs: the operator refuses at
\* most this many entries, which keeps the state space finite in practice.
OneClaim  == Cardinality(claims) <= 1
TwoClaims == Cardinality(claims) <= 2
====
