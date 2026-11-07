---- MODULE MCBig ----
EXTENDS AccountableSaga
\* 4 orgs, 3 steps. Step 3 is honest-to-honest when Byz = {"d"};
\* with Byz = {"c","d"}, step 1's owner AND beneficiary can collude.
MCOwner == <<"d", "a", "b">>
MCBenef == <<"c", "d", "c">>
====
