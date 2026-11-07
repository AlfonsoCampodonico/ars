--------------------------- MODULE AccountableSaga ---------------------------
(***************************************************************************)
(* Accountable Replicated Saga (ARS) -- formal model, v3.                 *)
(*                                                                         *)
(* A saga of steps arranged as a DAG runs across mutually distrusting     *)
(* orgs. Everything is anchored on a shared, append-only, timestamped     *)
(* LOG: every vote, attestation and receipt is a signed log entry, and    *)
(* every phase closes at a deadline. Outcomes are a pure function of the  *)
(* log, so all orgs agree. (LogFork.tla shows how that consistency        *)
(* assumption is enforced against a lying log operator.)                  *)
(*                                                                         *)
(* Each step s opens once all of Deps[s] have committed. It then runs:    *)
(*   1. PLAN   -- every org re-executes the deterministic plan and logs a *)
(*                vote: the result, or ABORT if it fails. Unanimous and   *)
(*                conflict-free => effect phase; anything else aborts.    *)
(*   2. EFFECT -- the OWNER performs the side effect and attests. If the  *)
(*                step has a trusted ORACLE (e.g. a payment processor),   *)
(*                the oracle's signed report decides. Otherwise the       *)
(*                BENEFICIARY confirms or disputes.                       *)
(*                                                                         *)
(* If any step aborts, the saga aborts: unfinished steps are cancelled,   *)
(* and a compensation window opens. Orgs undo committed steps in reverse  *)
(* topological order and log receipts; owners undo attested effects;     *)
(* beneficiaries (or oracles) check the undo.                             *)
(*                                                                         *)
(* When the saga finishes, SETTLEMENT runs on posted bonds: individually  *)
(* accused orgs are slashed, orgs in an unresolved dispute are frozen,    *)
(* everyone else gets their bond back.                                    *)
(*                                                                         *)
(* v3 adds: DAG-shaped sagas, trusted per-step oracles, bonds+slashing.   *)
(*                                                                         *)
(* v3.1: every window that waits on a RESPONSE is split in two, so that   *)
(* each deadline only waits on honest actions that were already possible *)
(* when its window opened -- which a fixed-length deadline can guarantee. *)
(*   effect phase   = "effect" (owner attests)  + "respond" (benef answers)*)
(*   compensation   = "open" (undo, receipts)   + "respond" (benef checks) *)
(* Found by the Go prototype's randomized test: a Byzantine owner that    *)
(* attests at the last instant of a single window leaves an honest        *)
(* beneficiary no time to answer, framing it as silent. On oracle steps   *)
(* the beneficiary has no duty at all: the oracle decides.                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Orgs,         \* participating organizations
    Byz,          \* the Byzantine subset (unknown to honest orgs)
    N,            \* number of steps
    Deps,         \* Deps[s]: steps that must commit before s opens
    Vals,         \* possible plan results (abstract result hashes)
    TruthVals,    \* what a correct plan execution may yield ("fail" = fails)
    Owner,        \* Owner[s]: org that performs step s's side effect
    Benef,        \* Benef[s]: org that observes step s's side effect
    OracleSteps   \* steps whose effect a trusted oracle reports on

Honest == Orgs \ Byz
Steps  == 1..N
Abort  == "abort"
Oracle == "oracle"

ASSUME
    /\ Byz \subseteq Orgs
    /\ N \in Nat \ {0}
    /\ Deps \in [Steps -> SUBSET Steps]
    /\ \A s \in Steps : \A d \in Deps[s] : d < s     \* numbered topologically
    /\ "abort" \notin Vals /\ "fail" \notin Vals
    /\ TruthVals \subseteq Vals \cup {"fail"}
    /\ Owner \in [Steps -> Orgs] /\ Benef \in [Steps -> Orgs]
    /\ \A s \in Steps : Owner[s] /= Benef[s]
    /\ OracleSteps \subseteq Steps

Vote(o, s, v)     == [k |-> "vote", from |-> o, step |-> s, val |-> v]
Entry(o, s, kind) == [k |-> kind,  from |-> o, step |-> s, val |-> "-"]

OrgKinds    == {"effect", "confirm", "dispute", "receipt", "undo", "undoOk", "undoDispute"}
OracleKinds == {"oDone", "oUndone"}
AllEntries ==
    {Vote(o, s, v) : o \in Orgs, s \in Steps, v \in Vals \cup {Abort}}
    \cup {Entry(o, s, k) : o \in Orgs, s \in Steps, k \in OrgKinds}
    \cup {Entry(Oracle, s, k) : s \in Steps, k \in OracleKinds}

Stages == {"pending", "plan", "effect", "respond", "committed", "aborted", "cancelled"}
Bonds  == {"held", "slashed", "frozen", "returned"}

VARIABLES
    truth,        \* truth[s]: deterministic re-executable plan result of step s
    log,          \* the shared append-only log
    stage,        \* stage[s] \in Stages
    effect,       \* effect[s] \in {"no","done","undone"}: the REAL side effect
    comp,         \* compensation: "none", "open", "respond" or "closed"
    compensated,  \* compensated[i]: committed steps honest i has locally undone
    bond          \* bond[o] \in Bonds

vars == <<truth, log, stage, effect, comp, compensated, bond>>

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

Attested(s)      == Has("effect", Owner[s], s)
Responded(s)     == Has("confirm", Benef[s], s) \/ Has("dispute", Benef[s], s)
UndoAttested(t)  == Has("undo", Owner[t], t)
UndoResponded(t) == Has("undoOk", Benef[t], t) \/ Has("undoDispute", Benef[t], t)
OracleDone(s)    == Has("oDone", Oracle, s)
OracleUndone(s)  == Has("oUndone", Oracle, s)

\* The beneficiary must answer an attestation -- except on oracle steps,
\* where the oracle decides and the beneficiary has no duty.
BenefDue(s)     == s \notin OracleSteps /\ Attested(s)
UndoBenefDue(t) == t \notin OracleSteps /\ UndoAttested(t)

Committed       == {s \in Steps : stage[s] = "committed"}
PlanClosed(s)   == stage[s] \in {"effect", "respond", "committed", "aborted"}
EffectClosed(s) == stage[s] \in {"committed", "aborted"} /\ PlanPassed(s)

\* Compensation obligations, computable from the log and stages.
OwesReceipt(t) == comp /= "none" /\ stage[t] = "committed"
OwesUndo(t)    == comp /= "none" /\ Attested(t)

EffectOK(s) ==
    /\ Attested(s)
    /\ IF s \in OracleSteps
          THEN OracleDone(s)
          ELSE Has("confirm", Benef[s], s) /\ ~Has("dispute", Benef[s], s)

HonestVote(s) == IF truth[s] = "fail" THEN Abort ELSE truth[s]

Finished == (\A s \in Steps : stage[s] = "committed") \/ comp = "closed"
Settled  == \A o \in Orgs : bond[o] /= "held"

-----------------------------------------------------------------------------
(* Evidence *)

Equivocated(o) ==
    \/ \E m1, m2 \in log : /\ m1.k = "vote" /\ m2.k = "vote"
                           /\ m1.from = o /\ m2.from = o
                           /\ m1.step = m2.step /\ m1.val /= m2.val
    \/ \E s \in Steps : Has("confirm", o, s) /\ Has("dispute", o, s)
    \/ \E s \in Steps : Has("undoOk", o, s) /\ Has("undoDispute", o, s)

BadVote(o) ==
    \E m \in log : /\ m.k = "vote" /\ m.from = o
                   /\ \/ m.val \in Vals /\ m.val /= truth[m.step]
                      \/ m.val = Abort  /\ truth[m.step] /= "fail"

SilentVoter(o) == \E s \in Steps : PlanClosed(s) /\ ~Voted(o, s)
SilentOwner(o) == \E s \in Steps : Owner[s] = o /\ EffectClosed(s) /\ ~Attested(s)
SilentBenef(o) == \E s \in Steps : Benef[s] = o /\ EffectClosed(s)
                                   /\ BenefDue(s) /\ ~Responded(s)

\* Oracle-settled lies: the trusted oracle contradicts a signed statement.
FalseAttest(o) ==
    \E s \in OracleSteps : Owner[s] = o /\ EffectClosed(s)
                           /\ Attested(s) /\ ~OracleDone(s)
FalseUndo(o) ==
    \E t \in OracleSteps : Owner[t] = o /\ comp = "closed"
                           /\ UndoAttested(t) /\ ~OracleUndone(t)
FalseDispute(o) ==
    \E s \in OracleSteps : Benef[s] = o /\
        \/ Has("dispute", o, s) /\ OracleDone(s)
        \/ Has("undoDispute", o, s) /\ OracleUndone(s)

Defaulted(o) ==
    /\ comp = "closed"
    /\ \/ \E t \in Steps : OwesReceipt(t) /\ ~Has("receipt", o, t)
       \/ \E t \in Steps : OwesUndo(t) /\ Owner[t] = o /\ ~UndoAttested(t)
       \/ \E t \in Steps : Benef[t] = o /\ UndoBenefDue(t) /\ ~UndoResponded(t)

Accused == {o \in Orgs : \/ Equivocated(o) \/ BadVote(o)
                         \/ SilentVoter(o) \/ SilentOwner(o) \/ SilentBenef(o)
                         \/ FalseAttest(o) \/ FalseUndo(o) \/ FalseDispute(o)
                         \/ Defaulted(o)}

\* Unresolved disputes exist only on steps WITHOUT an oracle.
Disputed == {{Owner[s], Benef[s]} :
                s \in {t \in Steps \ OracleSteps :
                          Has("dispute", Benef[t], t) \/ Has("undoDispute", Benef[t], t)}}

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ truth       \in [Steps -> TruthVals]
    /\ log         = {}
    /\ stage       = [s \in Steps |-> IF Deps[s] = {} THEN "plan" ELSE "pending"]
    /\ effect      = [s \in Steps |-> "no"]
    /\ comp        = "none"
    /\ compensated = [i \in Honest |-> {}]
    /\ bond        = [o \in Orgs |-> "held"]

-----------------------------------------------------------------------------
(* Honest org actions *)

HVote(i) ==
    \E s \in Steps :
        /\ stage[s] = "plan" /\ ~Voted(i, s)
        /\ log' = log \cup {Vote(i, s, HonestVote(s))}
        /\ UNCHANGED <<truth, stage, effect, comp, compensated, bond>>

HEffect(i) ==
    \E s \in Steps :
        /\ stage[s] = "effect" /\ Owner[s] = i /\ effect[s] = "no"
        /\ effect' = [effect EXCEPT ![s] = "done"]
        /\ log' = log \cup {Entry(i, s, "effect")}
        /\ UNCHANGED <<truth, stage, comp, compensated, bond>>

\* As beneficiary: check the real effect and confirm or dispute it.
HRespond(i) ==
    \E s \in Steps :
        /\ stage[s] \in {"effect", "respond"} /\ Benef[s] = i
        /\ BenefDue(s) /\ ~Responded(s)
        /\ log' = log \cup {Entry(i, s, IF effect[s] = "done" THEN "confirm" ELSE "dispute")}
        /\ UNCHANGED <<truth, stage, effect, comp, compensated, bond>>

\* Undo a committed step none of whose committed dependents is still live
\* (reverse topological order), then log a receipt.
HCompensate(i) ==
    LET P == {t \in Steps : OwesReceipt(t) /\ t \notin compensated[i]} IN
    \E t \in P :
        /\ comp = "open"
        /\ \A u \in P : t \notin Deps[u]
        /\ compensated' = [compensated EXCEPT ![i] = @ \cup {t}]
        /\ log' = log \cup {Entry(i, t, "receipt")}
        /\ UNCHANGED <<truth, stage, effect, comp, bond>>

HUndo(i) ==
    \E t \in Steps :
        /\ comp = "open" /\ OwesUndo(t) /\ Owner[t] = i /\ ~UndoAttested(t)
        /\ effect' = [effect EXCEPT ![t] = IF @ = "done" THEN "undone" ELSE @]
        /\ log' = log \cup {Entry(i, t, "undo")}
        /\ UNCHANGED <<truth, stage, comp, compensated, bond>>

HUndoRespond(i) ==
    \E t \in Steps :
        /\ comp \in {"open", "respond"} /\ Benef[t] = i
        /\ UndoBenefDue(t) /\ ~UndoResponded(t)
        /\ log' = log \cup {Entry(i, t, IF effect[t] /= "done" THEN "undoOk" ELSE "undoDispute")}
        /\ UNCHANGED <<truth, stage, effect, comp, compensated, bond>>

-----------------------------------------------------------------------------
(* Trusted oracle: reports the real state of an effect, truthfully and in  *)
(* time (before the relevant deadline).                                    *)

OracleReport ==
    \E s \in OracleSteps :
        \/ /\ stage[s] \in {"effect", "respond"} /\ effect[s] = "done" /\ ~OracleDone(s)
           /\ log' = log \cup {Entry(Oracle, s, "oDone")}
        \/ /\ comp \in {"open", "respond"} /\ effect[s] = "undone" /\ ~OracleUndone(s)
           /\ log' = log \cup {Entry(Oracle, s, "oUndone")}
    /\ UNCHANGED <<truth, stage, effect, comp, compensated, bond>>

-----------------------------------------------------------------------------
(* Deadlines. Guards encode partial synchrony: honest orgs and the oracle  *)
(* always act before a deadline. Byzantine orgs get no such courtesy.      *)

CommitStep(s) ==
    LET C == Committed \cup {s} IN
    stage' = [x \in Steps |->
                IF x = s THEN "committed"
                ELSE IF stage[x] = "pending" /\ Deps[x] \subseteq C THEN "plan"
                ELSE stage[x]]

\* Any abort aborts the whole saga: in-flight and pending steps are cancelled.
StartAbort(s) ==
    /\ stage' = [x \in Steps |->
                   IF x = s THEN "aborted"
                   ELSE IF stage[x] \in {"pending", "plan", "effect", "respond"} THEN "cancelled"
                   ELSE stage[x]]
    /\ comp' = "open"

ClosePlan(s) ==
    /\ stage[s] = "plan"
    /\ \A h \in Honest : Voted(h, s)
    /\ IF PlanPassed(s)
          THEN /\ stage' = [stage EXCEPT ![s] = "effect"]
               /\ UNCHANGED comp
          ELSE StartAbort(s)
    /\ UNCHANGED <<truth, log, effect, compensated, bond>>

\* End of the owner's window: no more attestations or real effects.
CloseAttest(s) ==
    /\ stage[s] = "effect"
    /\ Owner[s] \in Honest => Attested(s)
    /\ stage' = [stage EXCEPT ![s] = "respond"]
    /\ UNCHANGED <<truth, log, effect, comp, compensated, bond>>

\* End of the beneficiary's window. BenefDue(s) and effect[s] are frozen
\* since CloseAttest, so a fixed-length window suffices for this guard.
CloseEffect(s) ==
    /\ stage[s] = "respond"
    /\ (Benef[s] \in Honest /\ BenefDue(s)) => Responded(s)
    /\ TRUE
    /\ IF EffectOK(s)
          THEN /\ CommitStep(s) /\ UNCHANGED comp
          ELSE StartAbort(s)
    /\ UNCHANGED <<truth, log, effect, compensated, bond>>

\* End of the undo window: receipts and undo attestations are in.
CloseUndo ==
    /\ comp = "open"
    /\ \A h \in Honest, t \in Steps : OwesReceipt(t) => Has("receipt", h, t)
    /\ \A t \in Steps : (OwesUndo(t) /\ Owner[t] \in Honest) => UndoAttested(t)
    /\ comp' = "respond"
    /\ UNCHANGED <<truth, log, stage, effect, compensated, bond>>

\* End of compensation. UndoBenefDue and effects are frozen since CloseUndo.
CloseComp ==
    /\ comp = "respond"
    /\ \A t \in Steps : (Benef[t] \in Honest /\ UndoBenefDue(t)) => UndoResponded(t)
    /\ \A t \in OracleSteps : effect[t] = "undone" => OracleUndone(t)
    /\ comp' = "closed"
    /\ UNCHANGED <<truth, log, stage, effect, compensated, bond>>

\* Settlement on posted bonds, once the saga is over.
Settle ==
    /\ Finished /\ ~Settled
    /\ bond' = [o \in Orgs |->
                  IF o \in Accused THEN "slashed"
                  ELSE IF \E p \in Disputed : o \in p THEN "frozen"
                  ELSE "returned"]
    /\ UNCHANGED <<truth, log, stage, effect, comp, compensated>>

-----------------------------------------------------------------------------
(* Byzantine orgs: sign anything the log accepts (restricted to their own  *)
(* roles -- other entries are ignored by the protocol), do or skip effects.*)

BVote ==
    \E o \in Byz, s \in Steps, v \in Vals \cup {Abort} :
        /\ stage[s] = "plan" /\ Vote(o, s, v) \notin log
        /\ log' = log \cup {Vote(o, s, v)}
        /\ UNCHANGED <<truth, stage, effect, comp, compensated, bond>>

BPostEffectPhase ==
    \E o \in Byz, s \in Steps, kind \in {"effect", "confirm", "dispute"} :
        /\ IF kind = "effect" THEN Owner[s] = o /\ stage[s] = "effect"
                             ELSE Benef[s] = o /\ stage[s] \in {"effect", "respond"}
        /\ Entry(o, s, kind) \notin log
        /\ log' = log \cup {Entry(o, s, kind)}
        /\ UNCHANGED <<truth, stage, effect, comp, compensated, bond>>

BPostCompPhase ==
    \E o \in Byz, t \in Steps, kind \in {"receipt", "undo", "undoOk", "undoDispute"} :
        /\ CASE kind = "receipt" -> comp = "open" /\ OwesReceipt(t)
             [] kind = "undo"    -> comp = "open" /\ OwesUndo(t) /\ Owner[t] = o
             [] OTHER            -> comp \in {"open", "respond"} /\ Benef[t] = o
        /\ Entry(o, t, kind) \notin log
        /\ log' = log \cup {Entry(o, t, kind)}
        /\ UNCHANGED <<truth, stage, effect, comp, compensated, bond>>

BEffect ==
    \E s \in Steps :
        /\ Owner[s] \in Byz
        /\ \/ stage[s] = "effect" /\ effect[s] = "no"
              /\ effect' = [effect EXCEPT ![s] = "done"]
           \/ comp = "open" /\ effect[s] = "done"
              /\ effect' = [effect EXCEPT ![s] = "undone"]
        /\ UNCHANGED <<truth, log, stage, comp, compensated, bond>>

-----------------------------------------------------------------------------

Terminated == Settled /\ UNCHANGED vars

HonestStep(i) ==
    \/ HVote(i) \/ HEffect(i) \/ HRespond(i)
    \/ HCompensate(i) \/ HUndo(i) \/ HUndoRespond(i)

Next ==
    \/ \E i \in Honest : HonestStep(i)
    \/ OracleReport
    \/ \E s \in Steps : ClosePlan(s) \/ CloseAttest(s) \/ CloseEffect(s)
    \/ CloseUndo \/ CloseComp \/ Settle
    \/ BVote \/ BPostEffectPhase \/ BPostCompPhase \/ BEffect
    \/ Terminated

Fairness ==
    /\ \A i \in Honest : WF_vars(HonestStep(i))
    /\ WF_vars(OracleReport)
    /\ \A s \in Steps : WF_vars(ClosePlan(s)) /\ WF_vars(CloseAttest(s)) /\ WF_vars(CloseEffect(s))
    /\ WF_vars(CloseUndo) /\ WF_vars(CloseComp)
    /\ WF_vars(Settle)

Spec     == Init /\ [][Next]_vars
FairSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

TypeOK ==
    /\ truth \in [Steps -> TruthVals]
    /\ log \subseteq AllEntries
    /\ stage \in [Steps -> Stages]
    /\ effect \in [Steps -> {"no", "done", "undone"}]
    /\ comp \in {"none", "open", "respond", "closed"}
    /\ \A i \in Honest : compensated[i] \subseteq Steps
    /\ bond \in [Orgs -> Bonds]

\* No individual evidence ever names an honest org.
Accuracy == Accused \subseteq Byz

\* Every unresolved dispute involves at least one Byzantine org.
DisputeAccuracy == \A p \in Disputed : p \cap Byz /= {}

\* Every abort of a step that should have succeeded is attributable.
AbortAccountability ==
    \A s \in Steps :
        (stage[s] = "aborted" /\ truth[s] /= "fail") => (Accused /= {} \/ Disputed /= {})

\* NEW: on oracle steps, blame is always individual -- never a pair.
OracleAbortsNamed ==
    \A s \in OracleSteps :
        (stage[s] = "aborted" /\ truth[s] /= "fail") => Accused /= {}

Validity ==
    \A s \in Steps :
        stage[s] = "committed" => \A o \in Orgs : Vote(o, s, truth[s]) \in log

\* A committed effect really happened, if the beneficiary is honest or an
\* oracle vouched for it.
EffectIntegrity ==
    \A s \in Steps :
        (stage[s] = "committed" /\ (Benef[s] \in Honest \/ s \in OracleSteps))
            => effect[s] /= "no"

\* After compensation, every attested effect was undone or someone is blamed
\* (unless owner and beneficiary are both Byzantine and it's not an oracle step).
EffectsUndoneOrBlamed ==
    comp = "closed" =>
        \A t \in Steps :
            (OwesUndo(t) /\ ({Owner[t], Benef[t]} \cap Honest /= {} \/ t \in OracleSteps))
                => \/ effect[t] /= "done"
                   \/ Owner[t] \in Accused
                   \/ {Owner[t], Benef[t]} \in Disputed

HonestReceiptsTruthful ==
    \A i \in Honest, t \in Steps : Has("receipt", i, t) => t \in compensated[i]

HonestUndoOkTruthful ==
    \A t \in Steps : (Benef[t] \in Honest /\ Has("undoOk", Benef[t], t)) => effect[t] /= "done"

\* NEW (DAG): a step only opens once all its dependencies committed.
DepOrder ==
    \A s \in Steps :
        stage[s] \in {"plan", "effect", "respond", "committed", "aborted"}
            => \A d \in Deps[s] : stage[d] = "committed"

\* NEW (DAG): compensation runs in reverse topological order.
CompensationReverseTopo ==
    \A i \in Honest : \A t \in compensated[i], u \in Steps :
        (OwesReceipt(u) /\ t \in Deps[u]) => u \in compensated[i]

\* NEW (bonds): honest bonds are never slashed.
HonestNeverSlashed == \A o \in Honest : bond[o] /= "slashed"

\* NEW (bonds): an honest bond is frozen only when paired against a Byzantine org.
FrozenOnlyWithByz ==
    \A o \in Honest :
        bond[o] = "frozen" => \E p \in Disputed : o \in p /\ p \cap Byz /= {}

\* NEW (bonds): settlement is final -- no evidence appears after it, so every
\* accused org was slashed and nobody was slashed without evidence.
SettlementStable ==
    Settled => \A o \in Orgs : (bond[o] = "slashed") <=> (o \in Accused)

-----------------------------------------------------------------------------
(* Liveness *)

\* The saga always finishes and settles, even with silent Byzantine orgs.
Termination == <>Settled

-----------------------------------------------------------------------------
(* Non-vacuity witnesses: each is EXPECTED to be violated. *)

NoFullCompletion   == ~\A s \in Steps : stage[s] = "committed"
NoParallelism      == ~\E s, t \in Steps : s /= t /\ stage[s] \in {"effect", "respond"}
                                                   /\ stage[t] \in {"effect", "respond"}
NoCancelledUndo    == ~\E t \in Steps : stage[t] = "cancelled" /\ UndoAttested(t)
NoOracleCatch      == \A o \in Orgs : ~(FalseAttest(o) \/ FalseUndo(o) \/ FalseDispute(o))
NoDisputeEver      == Disputed = {}
NoSlash            == \A o \in Orgs : bond[o] /= "slashed"
NoFreeze           == \A o \in Orgs : bond[o] /= "frozen"

=============================================================================
