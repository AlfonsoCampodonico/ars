---- MODULE MCInv ----
EXTENDS AccountableSagaProofs
MCDeps   == <<{}, {}, {1, 2}>>
MCOwner  == <<"a", "c", "b">>
MCBenef  == <<"c", "b", "a">>
MCOracle == {1}
====
