------------------------ MODULE AccountableSagaProofs ------------------------
(***************************************************************************)
(* Machine-checked (TLAPS) proof that the Accountable Saga protocol never *)
(* blames an honest org:  Spec => []Accuracy,  for ANY number of orgs,    *)
(* Byzantine orgs, steps, values and any DAG, with an honest or a         *)
(* censoring log operator -- not just the small instances TLC enumerates.*)
(*                                                                         *)
(* Method: an inductive invariant Inv. Each conjunct pins down one way an *)
(* honest org could otherwise end up named by evidence. Duties are judged *)
(* on everything an org SIGNED (logged or claimed as refused), so the     *)
(* invariant holds whether or not the operator lets entries through.      *)
(*                                                                         *)
(* The step lemmas are generated (one goal per action and clause); see    *)
(* spec/gen_proofs.py.                                                    *)
(***************************************************************************)
EXTENDS AccountableSaga, TLAPS

\* The effect phase finished (committed, or aborted/held after a passed plan).
EffDone(s) == stage[s] = "committed" \/ (stage[s] \in {"aborted", "disputed"} /\ PlanPassed(s))
\* The owner's attestation window is over.
PastAttest(s) == stage[s] = "respond" \/ EffDone(s)

TypeInv ==
    /\ truth \in [Steps -> TruthVals]
    /\ \A m \in log : m.step \in Steps
    /\ \A c \in claims : c.e.step \in Steps
    /\ stage \in [Steps -> Stages]
    /\ effect \in [Steps -> {"no", "done", "undone"}]
    /\ comp \in {"none", "open", "respond", "closed", "held"}
    /\ compensated \in [Honest -> SUBSET Steps]
    /\ bond \in [Orgs -> Bonds]

\* I1: honest votes, logged or claimed, are always the correct re-execution.
I1 == \A m \in Signed : (m.k = "vote" /\ m.from \in Honest) => m.val = HonestVote(m.step)

\* I2: an honest beneficiary never contradicts itself, and never disputes on
\*     oracle steps (it has no duty there).
I2 == \A h \in Honest, s \in Steps :
        /\ s \in OracleSteps => (~Filed("dispute", h, s) /\ ~Filed("undoDispute", h, s))
        /\ ~(Filed("confirm", h, s) /\ Filed("dispute", h, s))
        /\ ~(Filed("undoOk", h, s) /\ Filed("undoDispute", h, s))

\* I3: once a plan closed, every honest org had voted.
I3 == \A s \in Steps : PlanClosed(s) => \A h \in Honest : FiledVote(h, s)

\* I4: once the attestation window closed, an honest owner had attested.
I4 == \A s \in Steps : (PastAttest(s) /\ Owner[s] \in Honest) => AttestFiled(s)

\* I5: once the effect phase finished, an honest beneficiary had answered.
I5 == \A s \in Steps : (EffDone(s) /\ Benef[s] \in Honest /\ BenefDue(s)) => RespondFiled(s)

\* I6: an honest owner only attests effects it really performed.
I6 == \A s \in Steps : (Owner[s] \in Honest /\ AttestFiled(s)) => effect[s] /= "no"

\* I7: the oracle reported every real effect before its phase finished.
I7 == \A s \in OracleSteps : (EffDone(s) /\ effect[s] /= "no") => OracleDoneFiled(s)

\* I8: nothing is undone unless compensation started.
I8 == comp \in {"none", "held"} => \A s \in Steps : effect[s] /= "undone"

\* I9: compensation or a hold only starts once no step is in flight.
I9 == comp /= "none" => \A s \in Steps : stage[s] \notin {"plan", "effect", "respond"}

\* I10: an honest owner's undo attestation is true.
I10 == \A t \in Steps : (Owner[t] \in Honest /\ UndoFiled(t)) => effect[t] = "undone"

\* I11: after the undo window, honest receipts and undos are all in.
I11 == comp \in {"respond", "closed"} =>
         /\ \A h \in Honest, t \in Steps : OwesReceipt(t) => Filed("receipt", h, t)
         /\ \A t \in Steps : (OwesUndo(t) /\ Owner[t] \in Honest) => UndoFiled(t)

\* I12: after compensation, honest undo checks and oracle refunds are in.
I12 == comp = "closed" =>
         /\ \A t \in Steps : (Benef[t] \in Honest /\ UndoBenefDue(t)) => UndoRespondFiled(t)
         /\ \A t \in OracleSteps : effect[t] = "undone" => OracleUndoneFiled(t)

Inv == TypeInv /\ I1 /\ I2 /\ I3 /\ I4 /\ I5 /\ I6 /\ I7 /\ I8 /\ I9 /\ I10 /\ I11 /\ I12

-----------------------------------------------------------------------------
(* Basic facts *)

LEMMA OracleSub == OracleSteps \subseteq Steps
  BY SagaAssumptions

\* Adding a log entry that is not a vote on step s leaves PlanPassed(s) as is.
LEMMA PPStable ==
  ASSUME NEW e, NEW s, log' = log \cup {e}, ~(e.k = "vote" /\ e.step = s)
  PROVE  PlanPassed(s)' <=> PlanPassed(s)
  BY DEF PlanPassed, CommitCert, AbortCert, VotesOn, Vote

LEMMA PPSame == ASSUME NEW s, log' = log PROVE PlanPassed(s)' <=> PlanPassed(s)
  BY DEF PlanPassed, CommitCert, AbortCert, VotesOn, Vote

-----------------------------------------------------------------------------
(* Base case *)

LEMMA InitInv == Init => Inv
<1> SUFFICES ASSUME Init PROVE Inv OBVIOUS
<1> USE DEF Init
<1>1. TypeInv
  BY DEF TypeInv, Stages, Bonds
<1>2. \A s \in Steps : stage[s] \in {"plan", "pending"}
  OBVIOUS
<1>3. Signed = {}
  BY DEF Signed
<1>9. \A k, o, s : ~Filed(k, o, s) /\ ~Has(k, o, s)
  BY <1>3 DEF Filed, Has
<1>4. I1 BY <1>3 DEF I1
<1>7. I2 BY <1>9 DEF I2
<1>8. I6 /\ I10 BY <1>9 DEF I6, I10, AttestFiled, UndoFiled
<1>5. I3 /\ I4 /\ I5 /\ I7
  BY OracleSub, <1>2 DEF I3, I4, I5, I7, PlanClosed, Closed, PastAttest, EffDone
<1>6. I8 /\ I9 /\ I11 /\ I12
  BY DEF I8, I9, I11, I12
<1> QED BY <1>1, <1>4, <1>5, <1>6, <1>7, <1>8 DEF Inv
-----------------------------------------------------------------------------
(* Inductive step, one lemma per action. *)
LEMMA Step_HVote ==
  ASSUME Inv, NEW i \in Honest, HVote(i)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, Post, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, Post, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, Post, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, Post, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, Post, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, Post, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, Post, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, Post, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, Post, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, Post, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, Post, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, Post, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, Post, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_HEffect ==
  ASSUME Inv, NEW i \in Honest, HEffect(i)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, Post, I9, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, Post, I9, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, Post, I9, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, Post, I9, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, Post, I9, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, Post, I9, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, Post, I9, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, Post, I9, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, Post, I9, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, Post, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, Post, I9, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, Post, I9, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, Post, I9, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_HRespond ==
  ASSUME Inv, NEW i \in Honest, HRespond(i)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, Post, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, Post, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, Post, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, Post, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, Post, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, Post, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, Post, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, Post, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, Post, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, Post, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, Post, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, Post, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, Post, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_HCompensate ==
  ASSUME Inv, NEW i \in Honest, HCompensate(i)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, Post, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, Post, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, Post, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, Post, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, Post, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, Post, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, Post, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, Post, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, Post, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, Post, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, Post, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, Post, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, Post, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_HUndo ==
  ASSUME Inv, NEW i \in Honest, HUndo(i)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, Post, I6, I9, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, Post, I6, I9, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, Post, I6, I9, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, Post, I6, I9, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, Post, I6, I9, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, Post, I6, I9, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, Post, I9, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, Post, I6, I9, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, Post, I6, I9, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, Post, I6, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, Post, I6, I9, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, Post, I6, I9, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, Post, I6, I9, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_HUndoRespond ==
  ASSUME Inv, NEW i \in Honest, HUndoRespond(i)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, Post, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, Post, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, Post, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, Post, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, Post, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, Post, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, Post, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, Post, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, Post, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, Post, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, Post, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, Post, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, Post, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_OracleReport ==
  ASSUME Inv, OracleReport
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, Post, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, Post, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, Post, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, Post, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, Post, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, Post, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, Post, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, Post, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, Post, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, Post, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, Post, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, Post, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, Post, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_ClosePlan ==
  ASSUME Inv, NEW s0 \in Steps, ClosePlan(s0)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, EndAt, Stages, Bonds, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, EndAt, Stages, Bonds, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, EndAt, Stages, Bonds, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, EndAt, Stages, Bonds, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, EndAt, Stages, Bonds, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, EndAt, Stages, Bonds, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, EndAt, Stages, Bonds, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, EndAt, Stages, Bonds, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, EndAt, Stages, Bonds, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, EndAt, Stages, Bonds, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, EndAt, Stages, Bonds, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, EndAt, Stages, Bonds, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, EndAt, Stages, Bonds, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_CloseAttest ==
  ASSUME Inv, NEW s0 \in Steps, CloseAttest(s0)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, Stages, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, Stages, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, Stages, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, Stages, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, Stages, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, Stages, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, Stages, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, Stages, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, Stages, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, Stages, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, Stages, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, Stages, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, Stages, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_CloseEffect ==
  ASSUME Inv, NEW s0 \in Steps, CloseEffect(s0)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, StartHold, EndAt, CommitStep, EffectOK, EffectDisputed, Committed, Stages, Bonds, I8, I9, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, StartHold, EndAt, CommitStep, EffectOK, EffectDisputed, Committed, Stages, Bonds, I8, I9, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, StartHold, EndAt, CommitStep, EffectOK, EffectDisputed, Committed, Stages, Bonds, I8, I9, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, StartHold, EndAt, CommitStep, EffectOK, EffectDisputed, Committed, Stages, Bonds, I8, I9, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, StartHold, EndAt, CommitStep, EffectOK, EffectDisputed, Committed, Stages, Bonds, I8, I9, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, StartHold, EndAt, CommitStep, EffectOK, EffectDisputed, Committed, Stages, Bonds, I8, I9, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, StartHold, EndAt, CommitStep, EffectOK, EffectDisputed, Committed, Stages, Bonds, I8, I9, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, StartHold, EndAt, CommitStep, EffectOK, EffectDisputed, Committed, Stages, Bonds, I8, I9, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, StartHold, EndAt, CommitStep, EffectOK, EffectDisputed, Committed, Stages, Bonds, I9, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, StartHold, EndAt, CommitStep, EffectOK, EffectDisputed, Committed, Stages, Bonds, I8, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, StartHold, EndAt, CommitStep, EffectOK, EffectDisputed, Committed, Stages, Bonds, I8, I9, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, StartHold, EndAt, CommitStep, EffectOK, EffectDisputed, Committed, Stages, Bonds, I8, I9, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, StartHold, EndAt, CommitStep, EffectOK, EffectDisputed, Committed, Stages, Bonds, I8, I9, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_CloseUndo ==
  ASSUME Inv, CloseUndo
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_CloseComp ==
  ASSUME Inv, CloseComp
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_Settle ==
  ASSUME Inv, Settle
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, Bonds, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, Bonds, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, Bonds, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, Bonds, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, Bonds, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, Bonds, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, Bonds, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, Bonds, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, Bonds, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, Bonds, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, Bonds, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, Bonds, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, Bonds, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_BVote ==
  ASSUME Inv, BVote
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, BPost, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, BPost, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, BPost, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, BPost, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, BPost, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, BPost, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, BPost, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, BPost, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, BPost, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, BPost, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, BPost, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, BPost, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, BPost, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_BPostEffectPhase ==
  ASSUME Inv, BPostEffectPhase
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, BPost, I9, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, BPost, I9, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, BPost, I9, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, BPost, I9, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, BPost, I9, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, BPost, I9, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, BPost, I9, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, BPost, I9, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, BPost, I9, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, BPost, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, BPost, I9, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, BPost, I9, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, BPost, I9, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_BPostCompPhase ==
  ASSUME Inv, BPostCompPhase
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, BPost, I9, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, BPost, I9, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, BPost, I9, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, BPost, I9, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, BPost, I9, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, BPost, I9, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, BPost, I9, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, BPost, I9, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, BPost, I9, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, BPost, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, BPost, I9, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, BPost, I9, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, BPost, I9, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_BEffect ==
  ASSUME Inv, BEffect
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I8, I9, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I8, I9, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I8, I9, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I8, I9, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I8, I9, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I8, I9, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I8, I9, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I8, I9, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I9, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I8, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I8, I9, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I8, I9, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I8, I9, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_Terminated ==
  ASSUME Inv, Terminated
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_UNCHANGEDvars ==
  ASSUME Inv, UNCHANGED vars
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, TypeInv, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I1, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I2, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I3, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I4, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I5, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I6, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I7, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I8, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I9, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I10, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I11, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I12, Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

THEOREM Inductive == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv' OBVIOUS
<1>1. CASE \E i \in Honest : HonestStep(i)
  BY <1>1, Step_HVote, Step_HEffect, Step_HRespond, Step_HCompensate, Step_HUndo, Step_HUndoRespond DEF HonestStep
<1>2. CASE \E s0 \in Steps : ClosePlan(s0) \/ CloseAttest(s0) \/ CloseEffect(s0)
  BY <1>2, Step_ClosePlan, Step_CloseAttest, Step_CloseEffect
<1>3. CASE OracleReport BY <1>3, Step_OracleReport
<1>4. CASE CloseUndo BY <1>4, Step_CloseUndo
<1>5. CASE CloseComp BY <1>5, Step_CloseComp
<1>6. CASE Settle BY <1>6, Step_Settle
<1>7. CASE BVote BY <1>7, Step_BVote
<1>8. CASE BPostEffectPhase BY <1>8, Step_BPostEffectPhase
<1>9. CASE BPostCompPhase BY <1>9, Step_BPostCompPhase
<1>10. CASE BEffect BY <1>10, Step_BEffect
<1>11. CASE Terminated BY <1>11, Step_Terminated
<1>12. CASE UNCHANGED vars BY <1>12, Step_UNCHANGEDvars
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12 DEF Next

THEOREM InvInvariant == Spec => []Inv
  BY InitInv, Inductive, PTL DEF Spec

-----------------------------------------------------------------------------
(* The invariant implies that no evidence ever names an honest org. *)

THEOREM InvAccuracy == Inv => Accuracy
<1> SUFFICES ASSUME Inv, NEW o \in Honest PROVE o \notin Accused
  BY DEF Accuracy, Accused, Honest
<1> USE DEF Inv, TypeInv, TypeOK
<1>0. o \in Orgs BY DEF Honest
<1>1. ~Equivocated(o)
  <2>1. ASSUME NEW m1 \in Signed, NEW m2 \in Signed, m1.k = "vote", m2.k = "vote",
               m1.from = o, m2.from = o, m1.step = m2.step
        PROVE  m1.val = m2.val
    BY <2>1 DEF I1
  <2>2. \A s \in Steps : ~(Filed("confirm", o, s) /\ Filed("dispute", o, s))
    BY DEF I2
  <2>3. \A s \in Steps : ~(Filed("undoOk", o, s) /\ Filed("undoDispute", o, s))
    BY DEF I2
  <2> QED BY <2>1, <2>2, <2>3 DEF Equivocated
<1>2. ~BadVote(o)
  <2> SUFFICES ASSUME NEW m \in Signed, m.k = "vote", m.from = o,
                      \/ m.val \in Vals /\ m.val /= truth[m.step]
                      \/ m.val = Abort /\ truth[m.step] /= "fail"
               PROVE FALSE
    BY DEF BadVote
  <2>1. m.val = HonestVote(m.step) BY DEF I1
  <2>2. m.step \in Steps BY DEF Signed
  <2>3. truth[m.step] \in TruthVals BY <2>2
  <2>4. truth[m.step] \in Vals \cup {"fail"} BY <2>3, SagaAssumptions
  <2> QED BY <2>1, <2>4, SagaAssumptions DEF HonestVote, Abort
<1>3. ~SilentVoter(o)
  BY DEF SilentVoter, I3
<1>4. ~SilentOwner(o)
  BY DEF SilentOwner, I4, PastAttest, EffDone, EffectClosed, Closed
<1>5. ~SilentBenef(o)
  BY DEF SilentBenef, I5, EffDone, EffectClosed, Closed
<1>6. ~FalseAttest(o)
  BY OracleSub DEF FalseAttest, I6, I7, EffDone, EffectClosed, Closed
<1>7. ~FalseUndo(o)
  BY OracleSub DEF FalseUndo, I10, I12
<1>8. ~FalseDispute(o)
  BY OracleSub DEF FalseDispute, I2
<1>9. ~Defaulted(o)
  BY DEF Defaulted, I11, I12
<1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF Accused

THEOREM SpecAccuracy == Spec => []Accuracy
  BY InvInvariant, InvAccuracy, PTL

=============================================================================
