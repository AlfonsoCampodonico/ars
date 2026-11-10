--------------------------- MODULE AccountableSaga ---------------------------
(***************************************************************************)
(* Accountable Replicated Saga (ARS) -- formal model, v4.                 *)
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
(*                                                                         *)
(* v4 closes three ways an honest org could still lose its bond:          *)
(*   - CENSORSHIP. The log operator may refuse an honest entry, so a      *)
(*     missing entry is no longer proof of silence. A refused org files a *)
(*     CLAIM (its signed entry, gossiped instead of logged). A claim      *)
(*     discharges the duty, and puts the org in an unresolved dispute     *)
(*     with the operator. If the operator had signed a RECEIPT for the    *)
(*     entry and then dropped it, the receipt proves it: the operator     *)
(*     alone is blamed.                                                   *)
(*   - IRREVERSIBLE STEPS. A PIVOT step (e.g. delivery) can't be undone.  *)
(*     It must be the saga's last step, so once it commits nothing can    *)
(*     abort; if it aborts, its owner owes no undo.                       *)
(*   - DISPUTES WITHOUT AN ORACLE. When nothing can tell which side lied, *)
(*     the saga HOLDS: nothing further commits or unwinds, and both bonds *)
(*     are frozen for outside resolution. Unwinding would pay whoever     *)
(*     disputes, so lying would pay.                                      *)
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
    OracleSteps,  \* steps whose effect a trusted oracle reports on
    Pivot,        \* steps whose effect cannot be undone
    OpByz         \* is the log operator Byzantine (may censor entries)?

Honest   == Orgs \ Byz
Steps    == 1..N
Abort    == "abort"
Oracle   == "oracle"
Operator == "operator"

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
    /\ {Oracle, Operator} \cap Orgs = {}
    /\ OpByz \in BOOLEAN
    \* A pivot is the last step and every other step leads to it, so it
    \* opens only once everything else committed.
    /\ Pivot \subseteq Steps
    /\ \A p \in Pivot : p = N /\ \A s \in 1..(N - 1) : \E u \in Steps : s \in Deps[u]

Vote(o, s, v)     == [k |-> "vote", from |-> o, step |-> s, val |-> v]
Entry(o, s, kind) == [k |-> kind,  from |-> o, step |-> s, val |-> "-"]

OrgKinds    == {"effect", "confirm", "dispute", "receipt", "undo", "undoOk", "undoDispute"}
OracleKinds == {"oDone", "oUndone"}
AllEntries ==
    {Vote(o, s, v) : o \in Orgs, s \in Steps, v \in Vals \cup {Abort}}
    \cup {Entry(o, s, k) : o \in Orgs, s \in Steps, k \in OrgKinds}
    \cup {Entry(Oracle, s, k) : s \in Steps, k \in OracleKinds}

\* A censorship claim: the signed entry, and whether the operator had
\* signed a receipt promising to include it.
Claim(e, r) == [e |-> e, rcpt |-> r]
AllClaims   == {Claim(e, r) : e \in AllEntries, r \in BOOLEAN}

Stages == {"pending", "plan", "effect", "respond", "committed", "aborted", "disputed", "cancelled"}
Bonds  == {"held", "slashed", "frozen", "returned"}

VARIABLES
    truth,        \* truth[s]: deterministic re-executable plan result of step s
    log,          \* the shared append-only log
    claims,       \* censorship claims, gossiped to every org before finality
    stage,        \* stage[s] \in Stages
    effect,       \* effect[s] \in {"no","done","undone"}: the REAL side effect
    comp,         \* "none", "open", "respond", "closed", or "held" (disputed, no unwinding)
    compensated,  \* compensated[i]: committed steps honest i has locally undone
    bond          \* bond[o] \in Bonds

vars == <<truth, log, claims, stage, effect, comp, compensated, bond>>

-----------------------------------------------------------------------------
(* Log queries. Outcomes are decided by the LOG alone. *)

Has(kind, o, s) == Entry(o, s, kind) \in log
VotesOn(s)      == {m \in log : m.k = "vote" /\ m.step = s}

CommitCert(s) == \E v \in Vals : \A o \in Orgs : Vote(o, s, v) \in log
AbortCert(s)  ==
    \/ \E m \in VotesOn(s) : m.val = Abort
    \/ \E m1, m2 \in VotesOn(s) : m1.val /= m2.val
PlanPassed(s) == CommitCert(s) /\ ~AbortCert(s)

Attested(s)     == Has("effect", Owner[s], s)
UndoAttested(t) == Has("undo", Owner[t], t)

\* The beneficiary must answer an attestation -- except on oracle steps,
\* where the oracle decides and the beneficiary has no duty.
BenefDue(s)     == s \notin OracleSteps /\ Attested(s)
UndoBenefDue(t) == t \notin OracleSteps /\ UndoAttested(t)

\* A non-oracle effect the beneficiary disputes: nobody can tell who lied.
EffectDisputed(s) == s \notin OracleSteps /\ Attested(s) /\ Has("dispute", Benef[s], s)

EffectOK(s) ==
    /\ Attested(s)
    /\ IF s \in OracleSteps
          THEN Has("oDone", Oracle, s)
          ELSE Has("confirm", Benef[s], s) /\ ~Has("dispute", Benef[s], s)

-----------------------------------------------------------------------------
(* Signed statements: what was logged plus what was claimed. Duties and    *)
(* evidence are judged on these, so a censored org is never "silent".      *)

Signed          == log \cup {c.e : c \in claims}
Filed(kind, o, s) == Entry(o, s, kind) \in Signed
FiledVote(o, s)   == \E m \in Signed : m.k = "vote" /\ m.from = o /\ m.step = s

AttestFiled(s)       == Filed("effect", Owner[s], s)
UndoFiled(t)         == Filed("undo", Owner[t], t)
RespondFiled(s)      == Filed("confirm", Benef[s], s) \/ Filed("dispute", Benef[s], s)
UndoRespondFiled(t)  == Filed("undoOk", Benef[t], t) \/ Filed("undoDispute", Benef[t], t)
OracleDoneFiled(s)   == Filed("oDone", Oracle, s)
OracleUndoneFiled(s) == Filed("oUndone", Oracle, s)

Committed     == {s \in Steps : stage[s] = "committed"}
Closed(s)     == stage[s] \in {"committed", "aborted", "disputed"}
PlanClosed(s) == stage[s] \in {"effect", "respond"} \/ Closed(s)
EffectClosed(s) == Closed(s) /\ PlanPassed(s)

\* Compensation obligations, computable from the log, claims and stages.
Compensating   == comp \in {"open", "respond", "closed"}
OwesReceipt(t) == Compensating /\ stage[t] = "committed"
OwesUndo(t)    == Compensating /\ t \notin Pivot /\ AttestFiled(t)

HonestVote(s) == IF truth[s] = "fail" THEN Abort ELSE truth[s]

Finished == (\A s \in Steps : stage[s] = "committed") \/ comp \in {"closed", "held"}
Settled  == \A o \in Orgs : bond[o] /= "held"

-----------------------------------------------------------------------------
(* Evidence *)

Equivocated(o) ==
    \/ \E m1, m2 \in Signed : /\ m1.k = "vote" /\ m2.k = "vote"
                              /\ m1.from = o /\ m2.from = o
                              /\ m1.step = m2.step /\ m1.val /= m2.val
    \/ \E s \in Steps : Filed("confirm", o, s) /\ Filed("dispute", o, s)
    \/ \E s \in Steps : Filed("undoOk", o, s) /\ Filed("undoDispute", o, s)

BadVote(o) ==
    \E m \in Signed : /\ m.k = "vote" /\ m.from = o
                      /\ \/ m.val \in Vals /\ m.val /= truth[m.step]
                         \/ m.val = Abort  /\ truth[m.step] /= "fail"

SilentVoter(o) == \E s \in Steps : PlanClosed(s) /\ ~\E m \in log : m.k = "vote" /\ m.from = o /\ m.step = s
SilentOwner(o) == \E s \in Steps : Owner[s] = o /\ EffectClosed(s) /\ ~AttestFiled(s)
SilentBenef(o) == \E s \in Steps : Benef[s] = o /\ EffectClosed(s)
                                   /\ BenefDue(s) /\ ~RespondFiled(s)

\* Oracle-settled lies: the trusted oracle contradicts a signed statement.
FalseAttest(o) ==
    \E s \in OracleSteps : Owner[s] = o /\ EffectClosed(s)
                           /\ AttestFiled(s) /\ ~OracleDoneFiled(s)
FalseUndo(o) ==
    \E t \in OracleSteps : Owner[t] = o /\ comp = "closed"
                           /\ UndoFiled(t) /\ ~OracleUndoneFiled(t)
FalseDispute(o) ==
    \E s \in OracleSteps : Benef[s] = o /\
        \/ Filed("dispute", o, s) /\ OracleDoneFiled(s)
        \/ Filed("undoDispute", o, s) /\ OracleUndoneFiled(s)

Defaulted(o) ==
    /\ comp = "closed"
    /\ \/ \E t \in Steps : OwesReceipt(t) /\ ~Filed("receipt", o, t)
       \/ \E t \in Steps : OwesUndo(t) /\ Owner[t] = o /\ ~UndoFiled(t)
       \/ \E t \in Steps : Benef[t] = o /\ UndoBenefDue(t) /\ ~UndoRespondFiled(t)

Accused == {o \in Orgs : \/ Equivocated(o) \/ BadVote(o)
                         \/ SilentVoter(o) \/ SilentOwner(o) \/ SilentBenef(o)
                         \/ FalseAttest(o) \/ FalseUndo(o) \/ FalseDispute(o)
                         \/ Defaulted(o)}

\* The operator signed a receipt for an entry and never logged it.
BrokenPromise == \E c \in claims : c.rcpt

\* Unresolved disputes: owner vs beneficiary on steps WITHOUT an oracle,
\* and an org (or the oracle) vs the operator on a refused entry.
EffectPairs == {{Owner[s], Benef[s]} :
                  s \in {t \in Steps \ OracleSteps :
                            Has("dispute", Benef[t], t) \/ Has("undoDispute", Benef[t], t)}}
CensorPairs == {{c.e.from, Operator} : c \in {d \in claims : ~d.rcpt}}
Disputed    == EffectPairs \cup CensorPairs

ByzParties == Byz \cup (IF OpByz THEN {Operator} ELSE {})

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ truth       \in [Steps -> TruthVals]
    /\ log         = {}
    /\ claims      = {}
    /\ stage       = [s \in Steps |-> IF Deps[s] = {} THEN "plan" ELSE "pending"]
    /\ effect      = [s \in Steps |-> "no"]
    /\ comp        = "none"
    /\ compensated = [i \in Honest |-> {}]
    /\ bond        = [o \in Orgs |-> "held"]

-----------------------------------------------------------------------------
(* Submitting a signed entry. An honest operator logs it. A Byzantine     *)
(* operator may refuse it instead (or sign a receipt and drop it), and    *)
(* the submitter then gossips a claim.                                    *)

Post(e) ==
    \/ log' = log \cup {e} /\ UNCHANGED claims
    \/ OpByz /\ \E r \in BOOLEAN : claims' = claims \cup {Claim(e, r)} /\ UNCHANGED log

\* A Byzantine org may also claim censorship falsely. Without a colluding
\* operator it can't produce a receipt.
BPost(e) ==
    \/ log' = log \cup {e} /\ UNCHANGED claims
    \/ \E r \in IF OpByz THEN BOOLEAN ELSE {FALSE} :
          claims' = claims \cup {Claim(e, r)} /\ UNCHANGED log

-----------------------------------------------------------------------------
(* Honest org actions *)

HVote(i) ==
    \E s \in Steps :
        /\ stage[s] = "plan" /\ ~FiledVote(i, s)
        /\ Post(Vote(i, s, HonestVote(s)))
        /\ UNCHANGED <<truth, stage, effect, comp, compensated, bond>>

HEffect(i) ==
    \E s \in Steps :
        /\ stage[s] = "effect" /\ Owner[s] = i /\ effect[s] = "no"
        /\ effect' = [effect EXCEPT ![s] = "done"]
        /\ Post(Entry(i, s, "effect"))
        /\ UNCHANGED <<truth, stage, comp, compensated, bond>>

\* As beneficiary: check the real effect and confirm or dispute it.
HRespond(i) ==
    \E s \in Steps :
        /\ stage[s] \in {"effect", "respond"} /\ Benef[s] = i
        /\ BenefDue(s) /\ ~RespondFiled(s)
        /\ Post(Entry(i, s, IF effect[s] = "done" THEN "confirm" ELSE "dispute"))
        /\ UNCHANGED <<truth, stage, effect, comp, compensated, bond>>

\* Undo a committed step none of whose committed dependents is still live
\* (reverse topological order), then log a receipt.
HCompensate(i) ==
    LET P == {t \in Steps : OwesReceipt(t) /\ t \notin compensated[i]} IN
    \E t \in P :
        /\ comp = "open"
        /\ \A u \in P : t \notin Deps[u]
        /\ compensated' = [compensated EXCEPT ![i] = @ \cup {t}]
        /\ Post(Entry(i, t, "receipt"))
        /\ UNCHANGED <<truth, stage, effect, comp, bond>>

\* A pivot's effect can't be undone, so an honest owner never claims to.
HUndo(i) ==
    \E t \in Steps \ Pivot :
        /\ comp = "open" /\ OwesUndo(t) /\ Owner[t] = i /\ ~UndoFiled(t)
        /\ effect' = [effect EXCEPT ![t] = IF @ = "done" THEN "undone" ELSE @]
        /\ Post(Entry(i, t, "undo"))
        /\ UNCHANGED <<truth, stage, comp, compensated, bond>>

HUndoRespond(i) ==
    \E t \in Steps :
        /\ comp \in {"open", "respond"} /\ Benef[t] = i
        /\ UndoBenefDue(t) /\ ~UndoRespondFiled(t)
        /\ Post(Entry(i, t, IF effect[t] /= "done" THEN "undoOk" ELSE "undoDispute"))
        /\ UNCHANGED <<truth, stage, effect, comp, compensated, bond>>

-----------------------------------------------------------------------------
(* Trusted oracle: reports the real state of an effect, truthfully and in  *)
(* time (before the relevant deadline).                                    *)

OracleReport ==
    \E s \in OracleSteps :
        \/ /\ stage[s] \in {"effect", "respond"} /\ effect[s] = "done" /\ ~OracleDoneFiled(s)
           /\ Post(Entry(Oracle, s, "oDone"))
        \/ /\ comp \in {"open", "respond"} /\ effect[s] = "undone" /\ ~OracleUndoneFiled(s)
           /\ Post(Entry(Oracle, s, "oUndone"))
    /\ UNCHANGED <<truth, stage, effect, comp, compensated, bond>>

-----------------------------------------------------------------------------
(* Deadlines. Guards encode partial synchrony: honest orgs and the oracle  *)
(* always act (log or claim) before a deadline. Byzantine orgs get no such *)
(* courtesy.                                                               *)

CommitStep(s) ==
    LET C == Committed \cup {s} IN
    stage' = [x \in Steps |->
                IF x = s THEN "committed"
                ELSE IF stage[x] = "pending" /\ Deps[x] \subseteq C THEN "plan"
                ELSE stage[x]]

\* End the saga early: step s takes stage `end`, everything unfinished is cancelled.
EndAt(s, end) ==
    stage' = [x \in Steps |->
                IF x = s THEN end
                ELSE IF stage[x] \in {"pending", "plan", "effect", "respond"} THEN "cancelled"
                ELSE stage[x]]

\* Any abort aborts the whole saga and opens compensation.
StartAbort(s) == EndAt(s, "aborted") /\ comp' = "open"

\* A dispute nobody can settle holds the saga: nothing more commits or unwinds.
StartHold(s) == EndAt(s, "disputed") /\ comp' = "held"

ClosePlan(s) ==
    /\ stage[s] = "plan"
    /\ \A h \in Honest : FiledVote(h, s)
    /\ IF PlanPassed(s)
          THEN /\ stage' = [stage EXCEPT ![s] = "effect"]
               /\ UNCHANGED comp
          ELSE StartAbort(s)
    /\ UNCHANGED <<truth, log, claims, effect, compensated, bond>>

\* End of the owner's window: no more attestations or real effects.
CloseAttest(s) ==
    /\ stage[s] = "effect"
    /\ Owner[s] \in Honest => AttestFiled(s)
    /\ stage' = [stage EXCEPT ![s] = "respond"]
    /\ UNCHANGED <<truth, log, claims, effect, comp, compensated, bond>>

\* End of the beneficiary's window. BenefDue(s) and effect[s] are frozen
\* since CloseAttest, so a fixed-length window suffices for this guard.
CloseEffect(s) ==
    /\ stage[s] = "respond"
    /\ (Benef[s] \in Honest /\ BenefDue(s)) => RespondFiled(s)
    /\ (s \in OracleSteps /\ effect[s] = "done") => OracleDoneFiled(s)
    /\ CASE EffectOK(s)       -> CommitStep(s) /\ UNCHANGED comp
         [] EffectDisputed(s) -> StartHold(s)
         [] OTHER             -> StartAbort(s)
    /\ UNCHANGED <<truth, log, claims, effect, compensated, bond>>

\* End of the undo window: receipts and undo attestations are in.
CloseUndo ==
    /\ comp = "open"
    /\ \A h \in Honest, t \in Steps : OwesReceipt(t) => Filed("receipt", h, t)
    /\ \A t \in Steps : (OwesUndo(t) /\ Owner[t] \in Honest) => UndoFiled(t)
    /\ comp' = "respond"
    /\ UNCHANGED <<truth, log, claims, stage, effect, compensated, bond>>

\* End of compensation. UndoBenefDue and effects are frozen since CloseUndo.
CloseComp ==
    /\ comp = "respond"
    /\ \A t \in Steps : (Benef[t] \in Honest /\ UndoBenefDue(t)) => UndoRespondFiled(t)
    /\ \A t \in OracleSteps : effect[t] = "undone" => OracleUndoneFiled(t)
    /\ comp' = "closed"
    /\ UNCHANGED <<truth, log, claims, stage, effect, compensated, bond>>

\* Settlement on posted bonds, once the saga is over.
Settle ==
    /\ Finished /\ ~Settled
    /\ bond' = [o \in Orgs |->
                  IF o \in Accused THEN "slashed"
                  ELSE IF \E p \in Disputed : o \in p THEN "frozen"
                  ELSE "returned"]
    /\ UNCHANGED <<truth, log, claims, stage, effect, comp, compensated>>

-----------------------------------------------------------------------------
(* Byzantine orgs: sign anything the log accepts (restricted to their own  *)
(* roles -- other entries are ignored by the protocol), log it or claim it *)
(* was refused, do or skip effects.                                        *)

BVote ==
    \E o \in Byz, s \in Steps, v \in Vals \cup {Abort} :
        /\ stage[s] = "plan" /\ Vote(o, s, v) \notin Signed
        /\ BPost(Vote(o, s, v))
        /\ UNCHANGED <<truth, stage, effect, comp, compensated, bond>>

BPostEffectPhase ==
    \E o \in Byz, s \in Steps, kind \in {"effect", "confirm", "dispute"} :
        /\ IF kind = "effect" THEN Owner[s] = o /\ stage[s] = "effect"
                             ELSE Benef[s] = o /\ stage[s] \in {"effect", "respond"}
        /\ Entry(o, s, kind) \notin Signed
        /\ BPost(Entry(o, s, kind))
        /\ UNCHANGED <<truth, stage, effect, comp, compensated, bond>>

BPostCompPhase ==
    \E o \in Byz, t \in Steps, kind \in {"receipt", "undo", "undoOk", "undoDispute"} :
        /\ CASE kind = "receipt" -> comp = "open" /\ OwesReceipt(t)
             [] kind = "undo"    -> comp = "open" /\ OwesUndo(t) /\ Owner[t] = o
             [] OTHER            -> comp \in {"open", "respond"} /\ Benef[t] = o
        /\ Entry(o, t, kind) \notin Signed
        /\ BPost(Entry(o, t, kind))
        /\ UNCHANGED <<truth, stage, effect, comp, compensated, bond>>

\* A pivot's effect can't be undone, by anyone.
BEffect ==
    \E s \in Steps :
        /\ Owner[s] \in Byz
        /\ \/ stage[s] = "effect" /\ effect[s] = "no"
              /\ effect' = [effect EXCEPT ![s] = "done"]
           \/ comp = "open" /\ effect[s] = "done" /\ s \notin Pivot
              /\ effect' = [effect EXCEPT ![s] = "undone"]
        /\ UNCHANGED <<truth, log, claims, stage, comp, compensated, bond>>

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
    /\ claims \subseteq AllClaims
    /\ stage \in [Steps -> Stages]
    /\ effect \in [Steps -> {"no", "done", "undone"}]
    /\ comp \in {"none", "open", "respond", "closed", "held"}
    /\ \A i \in Honest : compensated[i] \subseteq Steps
    /\ bond \in [Orgs -> Bonds]

\* No individual evidence ever names an honest org.
Accuracy == Accused \subseteq Byz

\* Every unresolved dispute involves at least one Byzantine party.
DisputeAccuracy == \A p \in Disputed : p \cap ByzParties /= {}

\* Only a Byzantine operator breaks a signed receipt.
OperatorAccuracy == BrokenPromise => OpByz

\* Every abort of a step that should have succeeded is attributable.
AbortAccountability ==
    \A s \in Steps :
        (stage[s] = "aborted" /\ truth[s] /= "fail")
            => (Accused /= {} \/ Disputed /= {} \/ BrokenPromise)

\* On oracle steps, blame is individual -- never an owner/beneficiary pair.
\* Only a censoring operator can leave such an abort without a named org.
OracleAbortsNamed ==
    \A s \in OracleSteps :
        (stage[s] = "aborted" /\ truth[s] /= "fail") => (Accused /= {} \/ claims /= {})

Validity ==
    \A s \in Steps :
        stage[s] = "committed" => \A o \in Orgs : Vote(o, s, truth[s]) \in log

\* A committed effect really happened, if the beneficiary is honest or an
\* oracle vouched for it.
EffectIntegrity ==
    \A s \in Steps :
        (stage[s] = "committed" /\ (Benef[s] \in Honest \/ s \in OracleSteps))
            => effect[s] /= "no"

\* After compensation, every effect owed an undo was undone or someone is
\* blamed (unless owner and beneficiary are both Byzantine and it's not an
\* oracle step).
EffectsUndoneOrBlamed ==
    comp = "closed" =>
        \A t \in Steps :
            (OwesUndo(t) /\ ({Owner[t], Benef[t]} \cap Honest /= {} \/ t \in OracleSteps))
                => \/ effect[t] /= "done"
                   \/ Owner[t] \in Accused
                   \/ {Owner[t], Benef[t]} \in Disputed
                   \/ {Owner[t], Operator} \in Disputed

HonestReceiptsTruthful ==
    \A i \in Honest, t \in Steps : Filed("receipt", i, t) => t \in compensated[i]

HonestUndoOkTruthful ==
    \A t \in Steps : (Benef[t] \in Honest /\ Filed("undoOk", Benef[t], t)) => effect[t] /= "done"

\* A step only opens once all its dependencies committed.
DepOrder ==
    \A s \in Steps :
        stage[s] \in {"plan", "effect", "respond", "committed", "aborted", "disputed"}
            => \A d \in Deps[s] : stage[d] = "committed"

\* Compensation runs in reverse topological order.
CompensationReverseTopo ==
    \A i \in Honest : \A t \in compensated[i], u \in Steps :
        (OwesReceipt(u) /\ t \in Deps[u]) => u \in compensated[i]

\* Honest bonds are never slashed.
HonestNeverSlashed == \A o \in Honest : bond[o] /= "slashed"

\* An honest bond is frozen only in a dispute with a Byzantine party.
FrozenOnlyWithByz ==
    \A o \in Honest :
        bond[o] = "frozen" => \E p \in Disputed : o \in p /\ p \cap ByzParties /= {}

\* Settlement is final: no evidence appears after it, so every accused org
\* was slashed and nobody was slashed without evidence.
SettlementStable ==
    Settled => \A o \in Orgs : (bond[o] = "slashed") <=> (o \in Accused)

\* NEW (v4): a disputed effect never triggers unwinding -- it holds instead.
NoUnwindOnDispute == \A s \in Steps : stage[s] = "aborted" => ~EffectDisputed(s)

\* NEW (v4): a held saga moves nothing back.
HoldUnwindsNothing == comp = "held" => \A s \in Steps : effect[s] /= "undone"

\* NEW (v4): once a pivot commits, the saga is complete -- nothing can abort.
PivotIsFinal ==
    \A p \in Pivot : stage[p] = "committed" => \A s \in Steps : stage[s] = "committed"

-----------------------------------------------------------------------------
(* Liveness *)

\* The saga always finishes and settles, even with silent Byzantine orgs
\* and a censoring operator.
Termination == <>Settled

-----------------------------------------------------------------------------
(* Non-vacuity witnesses: each is EXPECTED to be violated. *)

NoFullCompletion   == ~\A s \in Steps : stage[s] = "committed"
NoParallelism      == ~\E s, t \in Steps : s /= t /\ stage[s] \in {"effect", "respond"}
                                                   /\ stage[t] \in {"effect", "respond"}
NoCancelledUndo    == ~\E t \in Steps : stage[t] = "cancelled" /\ UndoAttested(t)
NoOracleCatch      == \A o \in Orgs : ~(FalseAttest(o) \/ FalseUndo(o) \/ FalseDispute(o))
NoDisputeEver      == EffectPairs = {}
NoSlash            == \A o \in Orgs : bond[o] /= "slashed"
NoFreeze           == \A o \in Orgs : bond[o] /= "frozen"
NoHold             == comp /= "held"
NoCensorship       == \A o \in Honest : ~\E c \in claims : c.e.from = o
NoBrokenPromise    == ~BrokenPromise
NoPivotAbortDone   == ~\E p \in Pivot : stage[p] = "aborted" /\ effect[p] = "done"

=============================================================================
