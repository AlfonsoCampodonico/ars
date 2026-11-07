--------------------------- MODULE AccountableSaga ---------------------------
(***************************************************************************)
(* Accountable Replicated Saga (ARS) -- formal model, v1.                 *)
(*                                                                         *)
(* A saga of N sequential steps is executed by a set of mutually          *)
(* distrusting organizations. Every org re-executes every step            *)
(* (replicated execution) and broadcasts a signed vote carrying the       *)
(* result it computed, or ABORT if execution failed.                      *)
(*                                                                         *)
(*   - Commit a step: an org has seen the SAME result signed by EVERY org.*)
(*   - Abort a step:  an org has seen any ABORT vote, or two different    *)
(*                    results for the same step.                          *)
(*   - On abort, each org compensates its committed steps in reverse,     *)
(*     then publishes a signed compensation receipt for every earlier     *)
(*     step.                                                              *)
(*                                                                         *)
(* v1 changes:                                                            *)
(*   - Justified vetoes: ABORT means "re-executing this step fails".      *)
(*     Steps are deterministic, so an ABORT on a step that succeeds is    *)
(*     evidence against the signer. There is no free veto any more.       *)
(*   - Enforced compensation: a clean abort certificate obliges EVERY     *)
(*     org to post a signed receipt for each earlier step to a public     *)
(*     log. Once the compensation deadline passes, a missing receipt is   *)
(*     proof of default.                                                  *)
(*                                                                         *)
(* Any number of orgs may be Byzantine. We promise accountability: if     *)
(* honest orgs disagree, a step is vetoed for no reason, or an org skips  *)
(* compensation, then public signed data identifies a Byzantine org, and *)
(* an honest org is never framed.                                         *)
(*                                                                         *)
(* Signatures are modelled abstractly: a vote or receipt "from o" can     *)
(* only appear through o's own action, so honest signatures are           *)
(* unforgeable. Byzantine orgs may sign anything, at any moment.          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Orgs,       \* all participating organizations
    Byz,        \* the Byzantine subset (unknown to honest orgs)
    N,          \* number of saga steps
    Vals,       \* possible step results (abstract result hashes)
    TruthVals   \* what a correct execution of a step may yield ("fail" = step fails)

ASSUME
    /\ Byz \subseteq Orgs
    /\ N \in Nat \ {0}
    /\ "abort" \notin Vals
    /\ "fail"  \notin Vals
    /\ TruthVals \subseteq Vals \cup {"fail"}

Honest   == Orgs \ Byz
Steps    == 1..N
Abort    == "abort"
VoteVals == Vals \cup {Abort}

Vote(o, s, v) == [from |-> o, step |-> s, val |-> v]
AllVotes      == {Vote(o, s, v) : o \in Orgs, s \in Steps, v \in VoteVals}

VARIABLES
    truth,        \* truth[s]: the deterministic, re-executable result of step s
    msgs,         \* every signed vote ever broadcast
    seen,         \* seen[i]: votes delivered to honest org i
    decision,     \* decision[i][s] \in {"none","commit","abort"}
    commitVal,    \* commitVal[i][s]: result i committed for step s
    cur,          \* cur[i]: step honest org i is working on
    phase,        \* phase[i] \in {"forward","compensating","done","aborted"}
    compensated,  \* compensated[i]: steps whose effects i has compensated
    receipts,     \* public log of signed receipts <<org, step>>: "step's effects undone"
    expired       \* abort points whose compensation deadline has passed

vars == <<truth, msgs, seen, decision, commitVal, cur, phase, compensated,
          receipts, expired>>

-----------------------------------------------------------------------------
(* Certificates: predicates anyone can evaluate over a set S of signed votes *)

\* Every org signed the same result for step t.
CommitCert(S, t) == \E v \in Vals : \A o \in Orgs : Vote(o, t, v) \in S

\* Step s must be aborted: someone reported failure, or results conflict.
AbortCert(S, s) ==
    \/ \E m \in S : m.step = s /\ m.val = Abort
    \/ \E m1, m2 \in S : m1.step = s /\ m2.step = s /\ m1.val /= m2.val

\* The saga cleanly aborted at s: every earlier step is certified committed,
\* s has an abort certificate, and no commit certificate competes with it.
\* At most one step can be a clean abort point.
CleanAbort(S, s) ==
    /\ AbortCert(S, s)
    /\ ~CommitCert(S, s)
    /\ \A t \in 1..(s - 1) : CommitCert(S, t)

-----------------------------------------------------------------------------
(* Helpers *)

HasVoted(i, s)  == \E m \in msgs : m.from = i /\ m.step = s
HonestVote(s)   == IF truth[s] = "fail" THEN Abort ELSE truth[s]

CanCommit(i, s, v) == v \in Vals /\ \A o \in Orgs : Vote(o, s, v) \in seen[i]
MustAbort(i, s)    == AbortCert(seen[i], s)

Committed(i)   == {t \in Steps : decision[i][t] = "commit"}
PendingComp(i) == Committed(i) \ compensated[i]
Max(S)         == CHOOSE x \in S : \A y \in S : y <= x

(* Evidence: what any third party can verify. *)
Equivocated(S, o) ==
    \E m1, m2 \in S : /\ m1.from = o /\ m2.from = o
                      /\ m1.step = m2.step /\ m1.val /= m2.val

\* Re-execution disagrees with a signed vote: a wrong result, or an ABORT
\* on a step that actually succeeds (an unjustified veto).
BadVote(S, o) ==
    \E m \in S : /\ m.from = o
                 /\ \/ m.val \in Vals /\ m.val /= truth[m.step]
                    \/ m.val = Abort  /\ truth[m.step] /= "fail"

Guilty(S) == {o \in Orgs : Equivocated(S, o) \/ BadVote(S, o)}

\* After the deadline for a clean abort at s, o has not receipted some t < s.
Defaulted(o) ==
    \E s \in expired :
        /\ CleanAbort(msgs, s)
        /\ \E t \in 1..(s - 1) : <<o, t>> \notin receipts

Accused == Guilty(msgs) \cup {o \in Orgs : Defaulted(o)}

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ truth       \in [Steps -> TruthVals]
    /\ msgs        = {}
    /\ seen        = [i \in Honest |-> {}]
    /\ decision    = [i \in Honest |-> [s \in Steps |-> "none"]]
    /\ commitVal   = [i \in Honest |-> [s \in Steps |-> "none"]]
    /\ cur         = [i \in Honest |-> 1]
    /\ phase       = [i \in Honest |-> "forward"]
    /\ compensated = [i \in Honest |-> {}]
    /\ receipts    = {}
    /\ expired     = {}

-----------------------------------------------------------------------------
(* Honest org actions *)

\* Re-execute the current step and sign the result, or ABORT if it fails.
\* (v1: there is no unjustified timeout vote; timeouts belong to the
\*  separate blocking/termination mechanism.)
Execute(i) ==
    LET s == cur[i]
        m == Vote(i, s, HonestVote(s))
    IN  /\ phase[i] = "forward"
        /\ ~HasVoted(i, s)
        /\ msgs' = msgs \cup {m}
        /\ seen' = [seen EXCEPT ![i] = @ \cup {m}]
        /\ UNCHANGED <<truth, decision, commitVal, cur, phase, compensated,
                       receipts, expired>>

\* The network delivers some broadcast vote to i (asynchronous, any order).
Deliver(i) ==
    \E m \in msgs \ seen[i] :
        /\ seen' = [seen EXCEPT ![i] = @ \cup {m}]
        /\ UNCHANGED <<truth, msgs, decision, commitVal, cur, phase,
                       compensated, receipts, expired>>

Commit(i) ==
    LET s == cur[i] IN
    /\ phase[i] = "forward"
    /\ HasVoted(i, s)
    /\ ~MustAbort(i, s)
    /\ \E v \in Vals :
        /\ CanCommit(i, s, v)
        /\ decision'  = [decision  EXCEPT ![i][s] = "commit"]
        /\ commitVal' = [commitVal EXCEPT ![i][s] = v]
    /\ IF s = N THEN /\ phase' = [phase EXCEPT ![i] = "done"]
                     /\ cur'   = cur
                ELSE /\ cur'   = [cur EXCEPT ![i] = s + 1]
                     /\ phase' = phase
    /\ UNCHANGED <<truth, msgs, seen, compensated, receipts, expired>>

AbortStep(i) ==
    LET s == cur[i] IN
    /\ phase[i] = "forward"
    /\ HasVoted(i, s)
    /\ MustAbort(i, s)
    /\ decision' = [decision EXCEPT ![i][s] = "abort"]
    /\ phase' = [phase EXCEPT ![i] =
                    IF Committed(i) = {} THEN "aborted" ELSE "compensating"]
    /\ UNCHANGED <<truth, msgs, seen, commitVal, cur, compensated,
                   receipts, expired>>

\* Undo the most recent committed, not-yet-compensated step.
Compensate(i) ==
    LET k == Max(PendingComp(i)) IN
    /\ phase[i] = "compensating"
    /\ PendingComp(i) /= {}
    /\ compensated' = [compensated EXCEPT ![i] = @ \cup {k}]
    /\ phase' = [phase EXCEPT ![i] =
                    IF PendingComp(i) = {k} THEN "aborted" ELSE "compensating"]
    /\ UNCHANGED <<truth, msgs, seen, decision, commitVal, cur,
                   receipts, expired>>

\* Once fully compensated, post a receipt for every step before the clean
\* abort point i knows of. For a step i never committed, the receipt
\* truthfully says "nothing to undo".
IssueReceipt(i) ==
    \E s \in Steps, t \in Steps :
        /\ t < s
        /\ phase[i] = "aborted"
        /\ CleanAbort(seen[i], s)
        /\ <<i, t>> \notin receipts
        /\ receipts' = receipts \cup {<<i, t>>}
        /\ UNCHANGED <<truth, msgs, seen, decision, commitVal, cur, phase,
                       compensated, expired>>

-----------------------------------------------------------------------------
(* The compensation deadline for clean abort point s passes.               *)
(* Partial-synchrony assumption: the deadline is long enough for every     *)
(* honest org to learn the abort and post its receipts. That is the guard. *)

Deadline(s) ==
    /\ s \notin expired
    /\ CleanAbort(msgs, s)
    /\ \A i \in Honest, t \in 1..(s - 1) : <<i, t>> \in receipts
    /\ expired' = expired \cup {s}
    /\ UNCHANGED <<truth, msgs, seen, decision, commitVal, cur, phase,
                   compensated, receipts>>

-----------------------------------------------------------------------------
(* Byzantine orgs sign whatever they like, including conflicting votes,   *)
(* and post receipts or withhold them as they please.                     *)

ByzVote ==
    \E o \in Byz, s \in Steps, v \in VoteVals :
        /\ Vote(o, s, v) \notin msgs
        /\ msgs' = msgs \cup {Vote(o, s, v)}
        /\ UNCHANGED <<truth, seen, decision, commitVal, cur, phase,
                       compensated, receipts, expired>>

\* Receipts only matter once some clean abort exists, so we restrict
\* Byzantine receipts to that case to keep the state space small.
ByzReceipt ==
    \E o \in Byz, s \in Steps, t \in Steps :
        /\ t < s
        /\ CleanAbort(msgs, s)
        /\ <<o, t>> \notin receipts
        /\ receipts' = receipts \cup {<<o, t>>}
        /\ UNCHANGED <<truth, msgs, seen, decision, commitVal, cur, phase,
                       compensated, expired>>

Terminated ==
    /\ \A i \in Honest : phase[i] \in {"done", "aborted"}
    /\ UNCHANGED vars

HonestStep(i) ==
    \/ Execute(i) \/ Deliver(i)    \/ Commit(i)
    \/ AbortStep(i) \/ Compensate(i) \/ IssueReceipt(i)

Next ==
    \/ \E i \in Honest : HonestStep(i)
    \/ \E s \in Steps : Deadline(s)
    \/ ByzVote \/ ByzReceipt
    \/ Terminated

Fairness ==
    \A i \in Honest :
        /\ WF_vars(Execute(i))
        /\ WF_vars(Deliver(i))
        /\ WF_vars(Commit(i))
        /\ WF_vars(AbortStep(i))
        /\ WF_vars(Compensate(i))
        /\ WF_vars(IssueReceipt(i))

Spec     == Init /\ [][Next]_vars
FairSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ truth \in [Steps -> TruthVals]
    /\ msgs \subseteq AllVotes
    /\ \A i \in Honest : seen[i] \subseteq msgs
    /\ decision  \in [Honest -> [Steps -> {"none", "commit", "abort"}]]
    /\ commitVal \in [Honest -> [Steps -> Vals \cup {"none"}]]
    /\ cur       \in [Honest -> Steps]
    /\ phase     \in [Honest -> {"forward", "compensating", "done", "aborted"}]
    /\ \A i \in Honest : compensated[i] \subseteq Steps
    /\ receipts \subseteq Orgs \X Steps
    /\ expired  \subseteq Steps

\* Honest orgs sign at most one vote per step.
HonestSingleVote ==
    \A m1, m2 \in msgs : (m1.from \in Honest /\ m1.from = m2.from
                          /\ m1.step = m2.step) => m1 = m2

\* Accuracy: no evidence -- equivocation, bad vote, or default --
\* ever implicates an honest org.
Accuracy == Accused \subseteq Byz

\* Accountable agreement: if two honest orgs decide differently on a step,
\* the votes they hold between them prove a Byzantine org misbehaved.
AccountableAgreement ==
    \A i, j \in Honest, s \in Steps :
        (decision[i][s] = "commit" /\ decision[j][s] = "abort")
            => Guilty(seen[i] \cup seen[j]) /= {}

\* NEW (gap 1): no free vetoes. If an honest org aborts a step that would
\* have succeeded, the votes it ALONE holds already prove who caused it.
VetoAccountability ==
    \A i \in Honest, s \in Steps :
        (decision[i][s] = "abort" /\ truth[s] /= "fail")
            => Guilty(seen[i]) /= {}

\* NEW (gap 2): honest receipts never lie. An honest org only claims a
\* step is undone if it never applied it or has compensated it.
HonestReceiptsTruthful ==
    \A r \in receipts :
        r[1] \in Honest =>
            (r[2] \notin Committed(r[1]) \/ r[2] \in compensated[r[1]])

\* NEW (gap 2): after the deadline, every org has either receipted every
\* owed step or is publicly accused. Nobody escapes compensation silently.
CompensationAccountable ==
    \A s \in expired :
        CleanAbort(msgs, s) =>
            \A o \in Orgs :
                \/ \A t \in 1..(s - 1) : <<o, t>> \in receipts
                \/ o \in Accused

\* Validity: a committed result is the correct (re-executable) result.
Validity ==
    \A i \in Honest, s \in Steps :
        decision[i][s] = "commit" => commitVal[i][s] = truth[s]

\* Honest orgs never commit different results for the same step.
CommitConsistency ==
    \A i, j \in Honest, s \in Steps :
        (decision[i][s] = "commit" /\ decision[j][s] = "commit")
            => commitVal[i][s] = commitVal[j][s]

\* With no Byzantine orgs, honest orgs simply agree.
AgreementIfAllHonest ==
    Byz = {} =>
        \A i, j \in Honest, s \in Steps :
            ~(decision[i][s] = "commit" /\ decision[j][s] = "abort")

\* Saga ordering: a step is decided only after all earlier steps committed.
SagaOrder ==
    \A i \in Honest, s \in Steps :
        decision[i][s] /= "none" => \A t \in 1..(s - 1) : decision[i][t] = "commit"

\* Only committed steps are compensated, and only after a later step aborted.
CompensationSoundness ==
    \A i \in Honest : \A s \in compensated[i] :
        /\ decision[i][s] = "commit"
        /\ \E t \in Steps : t > s /\ decision[i][t] = "abort"

\* Compensation runs in reverse order: never undo s while a later step is live.
CompensationReverseOrder ==
    \A i \in Honest : \A s \in compensated[i], t \in Committed(i) :
        t > s => t \in compensated[i]

\* "aborted" means every committed step has been undone.
AbortedIsClean ==
    \A i \in Honest : phase[i] = "aborted" => PendingComp(i) = {}

-----------------------------------------------------------------------------
(* Liveness *)

\* Every honest org ends either completed or fully compensated.
Termination == <>(\A i \in Honest : phase[i] \in {"done", "aborted"})

\* NEW: once the saga cleanly aborts, every honest org eventually posts all
\* its receipts -- even with Byzantine orgs, because a clean abort comes
\* with all the certificates honest orgs need to get there. (The abort may
\* also stop being clean if a Byzantine org later completes a commit
\* certificate, which is itself an equivocation.)
ReceiptLiveness ==
    \A s \in Steps :
        CleanAbort(msgs, s) ~>
            \/ ~CleanAbort(msgs, s)
            \/ \A i \in Honest, t \in 1..(s - 1) : <<i, t>> \in receipts

-----------------------------------------------------------------------------
(* Non-vacuity witnesses: each is EXPECTED to be violated. A counterexample *)
(* shows the scenario is reachable.                                        *)

NoDisagreementEver ==
    ~\E i, j \in Honest, s \in Steps :
        decision[i][s] = "commit" /\ decision[j][s] = "abort"

NoFullCompletion  == ~\E i \in Honest : phase[i] = "done"
NoCompensationRun == ~\E i \in Honest : compensated[i] /= {}

\* A healthy step really can be vetoed (and VetoAccountability catches it).
NoUnjustifiedVeto ==
    ~\E i \in Honest, s \in Steps : decision[i][s] = "abort" /\ truth[s] /= "fail"

\* A Byzantine org really can skip compensation (and gets accused).
NoDefaultEver == \A o \in Orgs : ~Defaulted(o)

=============================================================================
