---- MODULE MC ----
EXTENDS AccountableSaga
\* Step 1: honest a pays Byzantine c. Step 2: Byzantine c pays honest b.
MCOwner == <<"a", "c">>
MCBenef == <<"c", "b">>
====
