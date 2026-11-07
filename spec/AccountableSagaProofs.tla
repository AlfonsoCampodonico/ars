------------------------ MODULE AccountableSagaProofs ------------------------
(***************************************************************************)
(* Machine-checked (TLAPS) proof that the Accountable Saga protocol never *)
(* blames an honest org:  Spec => []Accuracy,  for ANY number of orgs,    *)
(* Byzantine orgs, steps, values and any DAG -- not just the small        *)
(* instances TLC can enumerate.                                           *)
(*                                                                         *)
(* Method: an inductive invariant Inv. Each conjunct pins down one way an *)
(* honest org could otherwise end up named by evidence.                   *)
(***************************************************************************)
EXTENDS AccountableSaga, TLAPS

\* The effect phase finished (committed, or aborted after a passed plan).
EffDone(s) == stage[s] = "committed" \/ (stage[s] = "aborted" /\ PlanPassed(s))
\* The owner's attestation window is over.
PastAttest(s) == stage[s] = "respond" \/ EffDone(s)

TypeInv ==
    /\ truth \in [Steps -> TruthVals]
    /\ \A m \in log : m.step \in Steps
    /\ stage \in [Steps -> Stages]
    /\ effect \in [Steps -> {"no", "done", "undone"}]
    /\ comp \in {"none", "open", "respond", "closed"}
    /\ compensated \in [Honest -> SUBSET Steps]
    /\ bond \in [Orgs -> Bonds]

\* I1: honest votes are always the correct re-execution result.
I1 == \A m \in log : (m.k = "vote" /\ m.from \in Honest) => m.val = HonestVote(m.step)

\* I2: an honest beneficiary never contradicts itself, and never disputes on
\*     oracle steps (it has no duty there).
I2 == \A h \in Honest, s \in Steps :
        /\ s \in OracleSteps => (~Has("dispute", h, s) /\ ~Has("undoDispute", h, s))
        /\ ~(Has("confirm", h, s) /\ Has("dispute", h, s))
        /\ ~(Has("undoOk", h, s) /\ Has("undoDispute", h, s))

\* I3: once a plan closed, every honest org had voted.
I3 == \A s \in Steps : PlanClosed(s) => \A h \in Honest : Voted(h, s)

\* I4: once the attestation window closed, an honest owner had attested.
I4 == \A s \in Steps : (PastAttest(s) /\ Owner[s] \in Honest) => Attested(s)

\* I5: once the effect phase finished, an honest beneficiary had answered.
I5 == \A s \in Steps : (EffDone(s) /\ Benef[s] \in Honest /\ BenefDue(s)) => Responded(s)

\* I6: an honest owner only attests effects it really performed.
I6 == \A s \in Steps : (Owner[s] \in Honest /\ Attested(s)) => effect[s] /= "no"

\* I7: the oracle reported every real effect before its phase finished.
I7 == \A s \in OracleSteps : (EffDone(s) /\ effect[s] /= "no") => OracleDone(s)

\* I8: nothing is undone before compensation starts.
I8 == comp = "none" => \A s \in Steps : effect[s] /= "undone"

\* I9: compensation only starts once no step is in flight.
I9 == comp /= "none" => \A s \in Steps : stage[s] \notin {"plan", "effect", "respond"}

\* I10: an honest owner's undo attestation is true.
I10 == \A t \in Steps : (Owner[t] \in Honest /\ UndoAttested(t)) => effect[t] = "undone"

\* I11: after the undo window, honest receipts and undos are all in.
I11 == comp \in {"respond", "closed"} =>
         /\ \A h \in Honest, t \in Steps : OwesReceipt(t) => Has("receipt", h, t)
         /\ \A t \in Steps : (OwesUndo(t) /\ Owner[t] \in Honest) => UndoAttested(t)

\* I12: after compensation, honest undo checks and oracle refunds are in.
I12 == comp = "closed" =>
         /\ \A t \in Steps : (Benef[t] \in Honest /\ UndoBenefDue(t)) => UndoResponded(t)
         /\ \A t \in OracleSteps : effect[t] = "undone" => OracleUndone(t)

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
<1>3. \A k, o, s : ~Has(k, o, s)
  BY DEF Has
<1>4. I1 BY DEF I1
<1>7. I2 BY <1>3 DEF I2
<1>8. I6 /\ I10 BY <1>3 DEF I6, I10, Attested, UndoAttested
<1>5. I3 /\ I4 /\ I5 /\ I7
  BY OracleSub, <1>2 DEF I3, I4, I5, I7, PlanClosed, PastAttest, EffDone
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
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HVote, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_HEffect ==
  ASSUME Inv, NEW i \in Honest, HEffect(i)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF I9, HEffect, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HEffect, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_HRespond ==
  ASSUME Inv, NEW i \in Honest, HRespond(i)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HRespond, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_HCompensate ==
  ASSUME Inv, NEW i \in Honest, HCompensate(i)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HCompensate, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_HUndo ==
  ASSUME Inv, NEW i \in Honest, HUndo(i)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF I6, HUndo, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndo, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_HUndoRespond ==
  ASSUME Inv, NEW i \in Honest, HUndoRespond(i)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF HUndoRespond, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_OracleReport ==
  ASSUME Inv, OracleReport
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF OracleReport, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_ClosePlan ==
  ASSUME Inv, NEW s0 \in Steps, ClosePlan(s0)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Stages, Bonds, ClosePlan, StartAbort, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF ClosePlan, StartAbort, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_CloseAttest ==
  ASSUME Inv, NEW s0 \in Steps, CloseAttest(s0)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Stages, Bonds, CloseAttest, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseAttest, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_CloseEffect ==
  ASSUME Inv, NEW s0 \in Steps, CloseEffect(s0)
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Stages, Bonds, CloseEffect, StartAbort, CommitStep, EffectOK, Committed, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, CommitStep, EffectOK, Committed, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, CommitStep, EffectOK, Committed, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, CommitStep, EffectOK, Committed, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, CommitStep, EffectOK, Committed, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, CommitStep, EffectOK, Committed, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, CommitStep, EffectOK, Committed, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF I8, I9, CloseEffect, StartAbort, CommitStep, EffectOK, Committed, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, CommitStep, EffectOK, Committed, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, CommitStep, EffectOK, Committed, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, CommitStep, EffectOK, Committed, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF I9, CloseEffect, StartAbort, CommitStep, EffectOK, Committed, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseEffect, StartAbort, CommitStep, EffectOK, Committed, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_CloseUndo ==
  ASSUME Inv, CloseUndo
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseUndo, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_CloseComp ==
  ASSUME Inv, CloseComp
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF CloseComp, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_Settle ==
  ASSUME Inv, Settle
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Stages, Bonds, Settle, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Settle, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_BVote ==
  ASSUME Inv, BVote
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BVote, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_BPostEffectPhase ==
  ASSUME Inv, BPostEffectPhase
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostEffectPhase, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_BPostCompPhase ==
  ASSUME Inv, BPostCompPhase
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BPostCompPhase, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_BEffect ==
  ASSUME Inv, BEffect
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF BEffect, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_Terminated ==
  ASSUME Inv, Terminated
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF Terminated, vars, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13

LEMMA Step_UNCHANGEDvars ==
  ASSUME Inv, UNCHANGED vars
  PROVE Inv'
<1> USE DEF Inv, TypeInv
<1>1. TypeInv'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, TypeInv, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>2. I1'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I1, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>3. I2'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I2, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>4. I3'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I3, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>5. I4'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I4, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>6. I5'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I5, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>7. I6'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I6, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>8. I7'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I7, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>9. I8'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I8, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>10. I9'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I9, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>11. I10'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I10, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>12. I11'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I11, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
<1>13. I12'
  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF vars, I12, Has, Voted, PlanClosed, PastAttest, EffDone, Attested, Responded, BenefDue, UndoAttested, UndoResponded, UndoBenefDue, OracleDone, OracleUndone, OwesReceipt, OwesUndo, Entry, Vote, HonestVote, Honest, Abort
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
  <2>1. ASSUME NEW m1 \in log, NEW m2 \in log, m1.k = "vote", m2.k = "vote",
               m1.from = o, m2.from = o, m1.step = m2.step
        PROVE  m1.val = m2.val
    BY <2>1 DEF I1
  <2>2. \A s \in Steps : ~(Has("confirm", o, s) /\ Has("dispute", o, s))
    BY DEF I2
  <2>3. \A s \in Steps : ~(Has("undoOk", o, s) /\ Has("undoDispute", o, s))
    BY DEF I2
  <2> QED BY <2>1, <2>2, <2>3 DEF Equivocated
<1>2. ~BadVote(o)
  <2> SUFFICES ASSUME NEW m \in log, m.k = "vote", m.from = o,
                      \/ m.val \in Vals /\ m.val /= truth[m.step]
                      \/ m.val = Abort /\ truth[m.step] /= "fail"
               PROVE FALSE
    BY DEF BadVote
  <2>1. m.val = HonestVote(m.step) BY DEF I1
  <2>2. m.step \in Steps OBVIOUS
  <2>3. truth[m.step] \in TruthVals BY <2>2
  <2>4. truth[m.step] \in Vals \cup {"fail"} BY <2>3, SagaAssumptions
  <2> QED BY <2>1, <2>4, SagaAssumptions DEF HonestVote, Abort
<1>3. ~SilentVoter(o)
  BY DEF SilentVoter, I3
<1>4. ~SilentOwner(o)
  BY DEF SilentOwner, I4, PastAttest, EffDone, EffectClosed
<1>5. ~SilentBenef(o)
  BY DEF SilentBenef, I5, EffDone, EffectClosed
<1>6. ~FalseAttest(o)
  BY OracleSub DEF FalseAttest, I6, I7, EffDone, EffectClosed
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
