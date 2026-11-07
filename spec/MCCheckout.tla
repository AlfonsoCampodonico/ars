---- MODULE MCCheckout ----
(***************************************************************************)
(* Concrete instance: an AI shopping agent buys from a merchant's agent.  *)
(*                                                                         *)
(*   1 lock terms  plan: price/tax/total from the signed term sheet      *)
(*                 effect: merchant creates the order -> buyer sees it    *)
(*   2 pay         plan: amount + buyer's spend limit from the term sheet *)
(*                 effect: merchant captures payment -> buyer is charged  *)
(*                 ORACLE: the payment processor's signed webhook         *)
(*   3 reserve     plan: stock check + pickup slot                        *)
(*                 effect: merchant reserves + books pickup -> carrier    *)
(*   4 ship        plan: shipping manifest                                *)
(*                 effect: carrier delivers -> buyer confirms receipt     *)
(*                                                                         *)
(*   2 and 3 run in parallel after 1; 4 needs both.                       *)
(***************************************************************************)
EXTENDS AccountableSaga
CkDeps   == <<{}, {1}, {1}, {2, 3}>>
CkOwner  == <<"merchant", "merchant", "merchant", "carrier">>
CkBenef  == <<"buyer", "buyer", "carrier", "buyer">>
CkOracle == {2}
====
