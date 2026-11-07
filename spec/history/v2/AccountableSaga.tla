--------------------------- MODULE AccountableSaga ---------------------------
(***************************************************************************)
(* Accountable Replicated Saga (ARS) -- formal model, v2.                 *)
(*                                                                         *)
(* A saga of N sequential steps runs across mutually distrusting orgs.    *)
(* Everything is anchored on a shared, append-only, timestamped LOG:      *)
(* every vote, attestation and receipt is a signed entry on it, and every *)
(* phase of every step closes at a deadline. Outcomes are a pure          *)
(* function of what the log holds at each deadline, so all orgs agree.    *)
(*                                                                         *)
(* Each step s has two phases:                                            *)
(*   1. PLAN   -- every org re-executes the step's deterministic plan and *)
(*                logs a signed vote: the result, or ABORT if it fails.   *)
(*                Unanimous identical results and no conflict => effect   *)
(*                phase. Anything else, including a missing vote, aborts. *)
(*   2. EFFECT -- the step's OWNER performs the non-deterministic side    *)
(*                effect (e.g. an API call) and logs a signed attestation.*)
(*                The step's BENEFICIARY, who can observe the effect,     *)
(*                logs CONFIRM or DISPUTE. Confirmed => committed.        *)
(*                                                                         *)
(* On abort, a compensation window opens: every org undoes its local      *)
(* state for committed steps and logs receipts; owners undo attested      *)
(* effects and log an UNDO attestation that the beneficiary confirms or   *)
(* disputes.                                                              *)
(*                                                                         *)
(* v2 closes v1's open gaps:                                              *)
(*   - Blocking: deadlines close every phase. Silence is no longer a      *)
(*     stall; it is an abort plus evidence against the silent org.        *)
(*   - Evidence exchange: all evidence lives on the shared log.           *)
(*   - Non-deterministic steps: owner + beneficiary attestations. A       *)
(*     dispute proves one of the two lied.                                *)
(*                                                                         *)
(* Assumptions made explicit in the model:                                *)
(*   - The log is consistent (one view for everyone) and rejects entries  *)
(*     for phases that already closed. Equivocation by the log operator   *)
(*     is out of scope: use a transparency log with gossiped tree heads.  *)
(*   - Partial synchrony: deadlines are long enough for honest orgs to    *)
(*     act. That is the guard on every Close action.                      *)
(*   - Honest signatures are unforgeable: an entry "from o" only appears  *)
(*     through o's own action.                                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Orgs,       \* all participating organizations
    Byz,        \* the Byzantine subset (unknown to honest orgs)
    N,          \* number of saga steps
    Vals,       \* possible plan results (abstract result hashes)
    TruthVals,  \* what a correct plan execution may yield ("fail" = step fails)
    Owner,      \* Owner[s]: org that performs step s's side effect
    Benef       \* Benef[s]: org that observes step s's side effect

Honest == Orgs \ Byz
Steps  == 1..N
Abort  == "abort"

ASSUME
    /\ Byz \subseteq Orgs
    /\ N \in Nat \ {0}
    /\ "abort" \notin Vals /\ "fail" \notin Vals
    /\ TruthVals \subseteq Vals \cup {"fail"}
    /\ Owner \in [Steps -> Orgs]
    /\ Benef \in [Steps -> Orgs]
    /\ \A s \in Steps : Owner[s] /= Benef[s]

\* Log entries. "vote" carries a value; attestations carry "-".
Vote(o, s, v)    == [k |-> "vote", from |-> o, step |-> s, val |-> v]
Entry(o, s, kind) == [k |-> kind,  from |-> o, step |-> s, val |-> "-"]

AttKinds  == {"effect", "confirm", "dispute", "receipt", "undo", "undoOk", "undoDispute"}
AllEntries ==
    {Vote(o, s, v) : o \in Orgs, s \in Steps, v \in Vals \cup {Abort}}
    \cup {Entry(o, s, k) : o \in Orgs, s \in Steps, k \in AttKinds}

VARIABLES
    truth,        \* truth[s]: deterministic re-executable plan result of step s
    log,          \* the shared append-only log
    stage,        \* stage[s] \in {"pending","plan","effect","committed","aborted"}
    effect,       \* effect[s] \in {"no","done","undone"}: the REAL side effect
    abortAt,      \* step at which the saga aborted (0 = none)
    comp,         \* compensation window: "none", "open" or "closed"
    compensated   \* compensated[i]: committed steps honest i has locally undone

vars == <<truth, log, stage, effect, abortAt, comp, compensated>>

-----------------------------------------------------------------------------
(* Log queries *)

Has(kind, o, s) == Entry(o, s, kind) \in log
Voted(o, s)     == \E m \in log : m.k = "vote" /\ m.from = o /\ m.step = s
VotesOn(s)      == {m \in log : m.k = "vote" /\ m.step = s}

CommitCert(s) == \E v \in Vals : \A o \in Orgs : Vote(o, s, v) \in log
AbortCert(s)  ==
    \/ \E m \in VotesOn(s) : m.val = Abort
    \/ \E m1, m2 \in VotesOn(s) : m1.val /= m2.val
PlanPassed(s) == CommitCert(s) /\ ~AbortCert(s)

Attested(s)   == Has("effect", Owner[s], s)
Responded(s)  == Has("confirm", Benef[s], s) \/ Has("dispute", Benef[s], s)
UndoAttested(t) == Has("undo", Owner[t], t)
UndoResponded(t) == Has("undoOk", Benef[t], t) \/ Has("undoDispute", Benef[t], t)

\* Phase-closed predicates (stable once true).
PlanClosed(s)   == stage[s] \in {"effect", "committed", "aborted"}
EffectClosed(s) == stage[s] \in {"committed", "aborted"} /\ PlanPassed(s)

\* Compensation obligations, all computable from the log.
OwesReceipt(t) == abortAt > 0 /\ t < abortAt              \* committed steps
OwesUndo(t)    == abortAt > 0 /\ t <= abortAt /\ Attested(t) \* attested effects

HonestVote(s) == IF truth[s] = "fail" THEN Abort ELSE truth[s]
Max(S)        == CHOOSE x \in S : \A y \in S : y <= x

-----------------------------------------------------------------------------
(* Evidence *)

\* Two contradicting signed statements by the same org.
Equivocated(o) ==
    \/ \E m1, m2 \in log : /\ m1.k = "vote" /\ m2.k = "vote"
                           /\ m1.from = o /\ m2.from = o
                           /\ m1.step = m2.step /\ m1.val /= m2.val
    \/ \E s \in Steps : Has("confirm", o, s) /\ Has("dispute", o, s)
    \/ \E s \in Steps : Has("undoOk", o, s) /\ Has("undoDispute", o, s)

\* Re-execution contradicts a signed vote (wrong result or unjustified veto).
BadVote(o) ==
    \E m \in log : /\ m.k = "vote" /\ m.from = o
                   /\ \/ m.val \in Vals /\ m.val /= truth[m.step]
                      \/ m.val = Abort  /\ truth[m.step] /= "fail"

\* Silence past a deadline (provable because the log is timestamped).
SilentVoter(o) == \E s \in Steps : PlanClosed(s) /\ ~Voted(o, s)
SilentOwner(o) == \E s \in Steps : Owner[s] = o /\ EffectClosed(s) /\ ~Attested(s)
SilentBenef(o) == \E s \in Steps : Benef[s] = o /\ EffectClosed(s)
                                   /\ Attested(s) /\ ~Responded(s)

\* Default on compensation, once the compensation deadline has passed.
Defaulted(o) ==
    /\ comp = "closed"
    /\ \/ \E t \in Steps : OwesReceipt(t) /\ ~Has("receipt", o, t)
       \/ \E t \in Steps : OwesUndo(t) /\ Owner[t] = o /\ ~UndoAttested(t)
       \/ \E t \in Steps : Benef[t] = o /\ UndoAttested(t) /\ ~UndoResponded(t)

\* Orgs that public evidence names individually.
Accused == {o \in Orgs : \/ Equivocated(o) \/ BadVote(o)
                         \/ SilentVoter(o) \/ SilentOwner(o) \/ SilentBenef(o)
                         \/ Defaulted(o)}

\* Owner/beneficiary pairs locked in a dispute: one of the two lied, and the
\* protocol cannot tell which. Resolution is external (audit, arbitration).
Disputed == {{Owner[s], Benef[s]} :
                s \in {t \in Steps : Has("dispute", Benef[t], t)
                                     \/ Has("undoDispute", Benef[t], t)}}

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ truth       \in [Steps -> TruthVals]
    /\ log         = {}
    /\ stage       = [s \in Steps |-> IF s = 1 THEN "plan" ELSE "pending"]
    /\ effect      = [s \in Steps |-> "no"]
    /\ abortAt     = 0
    /\ comp        = "none"
    /\ compensated = [i \in Honest |-> {}]

-----------------------------------------------------------------------------
(* Honest org actions *)

\* Re-execute the plan of the open step and log the result (or ABORT).
HVote(i) ==
    \E s \in Steps :
        /\ stage[s] = "plan"
        /\ ~Voted(i, s)
        /\ log' = log \cup {Vote(i, s, HonestVote(s))}
        /\ UNCHANGED <<truth, stage, effect, abortAt, comp, compensated>>

\* As owner: perform the side effect, then attest to it.
HEffect(i) ==
    \E s \in Steps :
        /\ stage[s] = "effect" /\ Owner[s] = i /\ effect[s] = "no"
        /\ effect' = [effect EXCEPT ![s] = "done"]
        /\ log' = log \cup {Entry(i, s, "effect")}
        /\ UNCHANGED <<truth, stage, abortAt, comp, compensated>>

\* As beneficiary: check the real effect and confirm or dispute it.
HRespond(i) ==
    \E s \in Steps :
        /\ stage[s] = "effect" /\ Benef[s] = i
        /\ Attested(s) /\ ~Responded(s)
        /\ log' = log \cup {Entry(i, s, IF effect[s] = "done" THEN "confirm" ELSE "dispute")}
        /\ UNCHANGED <<truth, stage, effect, abortAt, comp, compensated>>

\* Undo local state for the newest committed step, then log a receipt.
HCompensate(i) ==
    LET P == {t \in Steps : OwesReceipt(t) /\ t \notin compensated[i]} IN
    /\ comp = "open"
    /\ P /= {}
    /\ compensated' = [compensated EXCEPT ![i] = @ \cup {Max(P)}]
    /\ log' = log \cup {Entry(i, Max(P), "receipt")}
    /\ UNCHANGED <<truth, stage, effect, abortAt, comp>>

\* As owner: undo an attested side effect, then attest to the undo.
HUndo(i) ==
    \E t \in Steps :
        /\ comp = "open" /\ OwesUndo(t) /\ Owner[t] = i /\ ~UndoAttested(t)
        /\ effect' = [effect EXCEPT ![t] = IF @ = "done" THEN "undone" ELSE @]
        /\ log' = log \cup {Entry(i, t, "undo")}
        /\ UNCHANGED <<truth, stage, abortAt, comp, compensated>>

\* As beneficiary: check the undo really happened.
HUndoRespond(i) ==
    \E t \in Steps :
        /\ comp = "open" /\ Benef[t] = i
        /\ UndoAttested(t) /\ ~UndoResponded(t)
        /\ log' = log \cup {Entry(i, t, IF effect[t] = "done" THEN "undoDispute" ELSE "undoOk")}
        /\ UNCHANGED <<truth, stage, effect, abortAt, comp, compensated>>

-----------------------------------------------------------------------------
(* Deadlines. Each guard is the partial-synchrony assumption: honest orgs  *)
(* always act before a deadline. Byzantine orgs get no such courtesy.      *)

StartAbort(s) ==
    /\ stage'   = [stage EXCEPT ![s] = "aborted"]
    /\ abortAt' = s
    /\ comp'    = "open"

ClosePlan(s) ==
    /\ stage[s] = "plan"
    /\ \A h \in Honest : Voted(h, s)
    /\ IF PlanPassed(s)
          THEN /\ stage' = [stage EXCEPT ![s] = "effect"]
               /\ UNCHANGED <<abortAt, comp>>
          ELSE StartAbort(s)
    /\ UNCHANGED <<truth, log, effect, compensated>>

CloseEffect(s) ==
    /\ stage[s] = "effect"
    /\ Owner[s] \in Honest => Attested(s)
    /\ (Benef[s] \in Honest /\ Attested(s)) => Responded(s)
    /\ IF Attested(s) /\ Has("confirm", Benef[s], s) /\ ~Has("dispute", Benef[s], s)
          THEN /\ stage' = IF s < N
                              THEN [stage EXCEPT ![s] = "committed", ![s + 1] = "plan"]
                              ELSE [stage EXCEPT ![s] = "committed"]
               /\ UNCHANGED <<abortAt, comp>>
          ELSE StartAbort(s)
    /\ UNCHANGED <<truth, log, effect, compensated>>

CloseComp ==
    /\ comp = "open"
    /\ \A h \in Honest, t \in Steps : OwesReceipt(t) => Has("receipt", h, t)
    /\ \A t \in Steps : (OwesUndo(t) /\ Owner[t] \in Honest) => UndoAttested(t)
    /\ \A t \in Steps : (Benef[t] \in Honest /\ UndoAttested(t)) => UndoResponded(t)
    /\ comp' = "closed"
    /\ UNCHANGED <<truth, log, stage, effect, abortAt, compensated>>

-----------------------------------------------------------------------------
(* Byzantine orgs: sign anything the log will accept, do or skip real     *)
(* effects. Entries are restricted to an org's own roles (anything else   *)
(* is ignored by the protocol) to keep the state space small.             *)

BVote ==
    \E o \in Byz, s \in Steps, v \in Vals \cup {Abort} :
        /\ stage[s] = "plan"
        /\ Vote(o, s, v) \notin log
        /\ log' = log \cup {Vote(o, s, v)}
        /\ UNCHANGED <<truth, stage, effect, abortAt, comp, compensated>>

BPostEffectPhase ==
    \E o \in Byz, s \in Steps, kind \in {"effect", "confirm", "dispute"} :
        /\ stage[s] = "effect"
        /\ IF kind = "effect" THEN Owner[s] = o ELSE Benef[s] = o
        /\ Entry(o, s, kind) \notin log
        /\ log' = log \cup {Entry(o, s, kind)}
        /\ UNCHANGED <<truth, stage, effect, abortAt, comp, compensated>>

BPostCompPhase ==
    \E o \in Byz, t \in Steps, kind \in {"receipt", "undo", "undoOk", "undoDispute"} :
        /\ comp = "open"
        /\ CASE kind = "receipt" -> OwesReceipt(t)
             [] kind = "undo"    -> OwesUndo(t) /\ Owner[t] = o
             [] OTHER            -> Benef[t] = o
        /\ Entry(o, t, kind) \notin log
        /\ log' = log \cup {Entry(o, t, kind)}
        /\ UNCHANGED <<truth, stage, effect, abortAt, comp, compensated>>

\* A Byzantine owner may perform or undo its real effect silently.
BEffect ==
    \E s \in Steps :
        /\ Owner[s] \in Byz
        /\ \/ stage[s] = "effect" /\ effect[s] = "no"
              /\ effect' = [effect EXCEPT ![s] = "done"]
           \/ comp = "open" /\ effect[s] = "done"
              /\ effect' = [effect EXCEPT ![s] = "undone"]
        /\ UNCHANGED <<truth, log, stage, abortAt, comp, compensated>>

-----------------------------------------------------------------------------

Finished == stage[N] = "committed" \/ comp = "closed"

Terminated == Finished /\ UNCHANGED vars

HonestStep(i) ==
    \/ HVote(i) \/ HEffect(i) \/ HRespond(i)
    \/ HCompensate(i) \/ HUndo(i) \/ HUndoRespond(i)

Next ==
    \/ \E i \in Honest : HonestStep(i)
    \/ \E s \in Steps : ClosePlan(s) \/ CloseEffect(s)
    \/ CloseComp
    \/ BVote \/ BPostEffectPhase \/ BPostCompPhase \/ BEffect
    \/ Terminated

Fairness ==
    /\ \A i \in Honest : WF_vars(HonestStep(i))
    /\ \A s \in Steps  : WF_vars(ClosePlan(s)) /\ WF_vars(CloseEffect(s))
    /\ WF_vars(CloseComp)

Spec     == Init /\ [][Next]_vars
FairSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

TypeOK ==
    /\ truth \in [Steps -> TruthVals]
    /\ log \subseteq AllEntries
    /\ stage \in [Steps -> {"pending", "plan", "effect", "committed", "aborted"}]
    /\ effect \in [Steps -> {"no", "done", "undone"}]
    /\ abortAt \in 0..N
    /\ comp \in {"none", "open", "closed"}
    /\ \A i \in Honest : compensated[i] \subseteq Steps

\* No evidence of any kind ever names an honest org.
Accuracy == Accused \subseteq Byz

\* Every dispute involves at least one Byzantine org.
DisputeAccuracy == \A p \in Disputed : p \cap Byz /= {}

\* Every abort of a step that should have succeeded is attributable: some org
\* is individually accused, or an owner/beneficiary pair is in dispute.
AbortAccountability ==
    \A s \in Steps :
        (stage[s] = "aborted" /\ truth[s] /= "fail") => (Accused /= {} \/ Disputed /= {})

\* A committed plan result is the correct re-executable result.
Validity ==
    \A s \in Steps :
        stage[s] = "committed" => \A o \in Orgs : Vote(o, s, truth[s]) \in log

\* An honest beneficiary is never left with a committed step whose effect
\* never happened.
EffectIntegrity ==
    \A s \in Steps :
        (stage[s] = "committed" /\ Benef[s] \in Honest) => effect[s] /= "no"

\* After compensation, every attested effect was really undone or someone is
\* blamed -- unless owner AND beneficiary are both Byzantine (then the effect
\* only concerns colluders).
EffectsUndoneOrBlamed ==
    comp = "closed" =>
        \A t \in Steps :
            (OwesUndo(t) /\ {Owner[t], Benef[t]} \cap Honest /= {})
                => \/ effect[t] /= "done"
                   \/ Owner[t] \in Accused
                   \/ {Owner[t], Benef[t]} \in Disputed

\* Honest receipts and undo confirmations never lie.
HonestReceiptsTruthful ==
    \A i \in Honest, t \in Steps : Has("receipt", i, t) => t \in compensated[i]

HonestUndoOkTruthful ==
    \A t \in Steps : (Benef[t] \in Honest /\ Has("undoOk", Benef[t], t)) => effect[t] /= "done"

\* Saga order: a step only starts once every earlier step committed.
SagaOrder ==
    \A s \in Steps :
        stage[s] /= "pending" => \A t \in 1..(s - 1) : stage[t] = "committed"

\* Local compensation runs newest-first.
CompensationReverseOrder ==
    \A i \in Honest : \A s \in compensated[i], t \in Steps :
        (OwesReceipt(t) /\ t > s) => t \in compensated[i]

-----------------------------------------------------------------------------
(* Liveness *)

\* NEW: the saga always finishes, even when Byzantine orgs go silent.
Termination == <>Finished

-----------------------------------------------------------------------------
(* Non-vacuity witnesses: each is EXPECTED to be violated. *)

NoFullCompletion  == stage[N] /= "committed"
NoCompensation    == comp /= "closed"
NoSilenceCaught   == \A o \in Orgs : ~(SilentVoter(o) \/ SilentOwner(o) \/ SilentBenef(o))
NoDisputeEver     == Disputed = {}
NoDefaultEver     == \A o \in Orgs : ~Defaulted(o)

=============================================================================
