------------------------------- MODULE LogFork -------------------------------
(***************************************************************************)
(* Discharging AccountableSaga's "consistent log" assumption.             *)
(*                                                                         *)
(* AccountableSaga treats the shared log as a single consistent view. In  *)
(* practice it is run by an operator who could equivocate: show org A a   *)
(* log where phase p committed and org B one where it aborted. This spec  *)
(* abstracts each phase's closing to a SIGNED HEAD -- the operator's      *)
(* signature over "phase p closed with outcome X" (a signed tree head).   *)
(*                                                                         *)
(* Mechanism:                                                             *)
(*   - Orgs act on the heads they receive, phase by phase.                *)
(*   - Orgs GOSSIP every head they hold to each other.                    *)
(*   - Two signed heads for the same phase with different outcomes are a  *)
(*     FORK PROOF against the operator.                                   *)
(*   - An operator can also withhold a head from some org. That org times *)
(*     out, aborts locally, and gossips a signed timeout claim. A commit  *)
(*     head next to a timeout claim for the same phase is a CONFLICT      *)
(*     (not proof of guilt -- withholding cannot be proven -- but enough  *)
(*     to know views diverged).                                           *)
(*   - ABORT DOMINANCE: an org that sees a conflict before FINALITY       *)
(*     abandons its view and compensates everything it applied.          *)
(*   - FINALITY: a deadline after the saga ends, long enough for a full   *)
(*     gossip round (partial synchrony). After it, outcomes never change; *)
(*     later forks only add evidence against the operator.                *)
(*                                                                         *)
(* Honest orgs only: Byzantine org behaviour is covered by the main spec. *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Orgs,     \* honest orgs
    N,        \* number of phases (one per saga step, linearised)
    OpByz     \* is the log operator Byzantine?

ASSUME N \in Nat \ {0} /\ OpByz \in BOOLEAN /\ Cardinality(Orgs) >= 2

Phases   == 1..N
Outcomes == {"commit", "abort"}

Head(p, o)  == [kind |-> "head",    p |-> p, x |-> o]   \* signed by operator
Claim(i, p) == [kind |-> "timeout", p |-> p, x |-> i]   \* signed by org i

VARIABLES
    heads,     \* every head the operator ever signed
    seen,      \* seen[i]: heads and claims org i holds
    pos,       \* pos[i]: phase org i is on
    st,        \* st[i] \in {"run", "done", "comp", "aborted"}
    outcome,   \* outcome[i][p]: what i acted on for phase p
    applied,   \* applied[i]: phases i applied (committed)
    undone,    \* undone[i]: applied phases i compensated
    final      \* finality deadline passed

vars == <<heads, seen, pos, st, outcome, applied, undone, final>>

-----------------------------------------------------------------------------

HeadFor(S, p) == {h \in S : h.kind = "head" /\ h.p = p}

\* Fork proof: the operator signed two different outcomes for one phase.
Fork(S) == \E h1, h2 \in S : h1.kind = "head" /\ h2.kind = "head"
                             /\ h1.p = h2.p /\ h1.x /= h2.x

\* Conflict: a fork, or a commit head for a phase someone timed out on.
Conflict(S) ==
    \/ Fork(S)
    \/ \E h \in S, c \in S : h.kind = "head" /\ h.x = "commit"
                             /\ c.kind = "timeout" /\ c.p = h.p

Max(S) == CHOOSE m \in S : \A y \in S : y <= m

-----------------------------------------------------------------------------

Init ==
    /\ heads   = {}
    /\ seen    = [i \in Orgs |-> {}]
    /\ pos     = [i \in Orgs |-> 1]
    /\ st      = [i \in Orgs |-> "run"]
    /\ outcome = [i \in Orgs |-> [p \in Phases |-> "none"]]
    /\ applied = [i \in Orgs |-> {}]
    /\ undone  = [i \in Orgs |-> {}]
    /\ final   = FALSE

-----------------------------------------------------------------------------
(* Log operator *)

\* Sign a head for phase p with outcome o and hand it to org i. An honest
\* operator never signs two outcomes for the same phase; a Byzantine one can,
\* at any time (even after finality).
Issue(i, p, o) ==
    /\ OpByz \/ \A h \in heads : h.p = p => h.x = o
    /\ Head(p, o) \notin seen[i]
    /\ heads' = heads \cup {Head(p, o)}
    /\ seen'  = [seen EXCEPT ![i] = @ \cup {Head(p, o)}]
    /\ UNCHANGED <<pos, st, outcome, applied, undone, final>>

\* Honest operator serves every org its current phase's head (liveness).
HonestServe(i) ==
    /\ ~OpByz
    /\ st[i] = "run" /\ HeadFor(seen[i], pos[i]) = {}
    /\ \E o \in Outcomes : Issue(i, pos[i], o)

-----------------------------------------------------------------------------
(* Orgs *)

Gossip(i, j) ==
    /\ i /= j /\ ~(seen[i] \subseteq seen[j])
    /\ seen' = [seen EXCEPT ![j] = @ \cup seen[i]]
    /\ UNCHANGED <<heads, pos, st, outcome, applied, undone, final>>

\* Act on the (single, unconflicted) head for the current phase.
Proceed(i) ==
    LET p == pos[i] IN
    /\ st[i] = "run" /\ ~Conflict(seen[i])
    /\ \E h \in HeadFor(seen[i], p) :
         /\ outcome' = [outcome EXCEPT ![i][p] = h.x]
         /\ IF h.x = "commit"
              THEN /\ applied' = [applied EXCEPT ![i] = @ \cup {p}]
                   /\ IF p = N THEN st' = [st EXCEPT ![i] = "done"] /\ pos' = pos
                               ELSE pos' = [pos EXCEPT ![i] = p + 1] /\ st' = st
              ELSE /\ st' = [st EXCEPT ![i] = "comp"]
                   /\ UNCHANGED <<applied, pos>>
    /\ UNCHANGED <<heads, seen, undone, final>>

\* No head arrived before the phase deadline: abort locally and say so.
\* (Partial synchrony: an honest operator always delivers in time.)
Timeout(i) ==
    LET p == pos[i] IN
    /\ OpByz
    /\ st[i] = "run" /\ HeadFor(seen[i], p) = {}
    /\ seen'    = [seen EXCEPT ![i] = @ \cup {Claim(i, p)}]
    /\ outcome' = [outcome EXCEPT ![i][p] = "abort"]
    /\ st'      = [st EXCEPT ![i] = "comp"]
    /\ UNCHANGED <<heads, pos, applied, undone, final>>

\* Abort dominance: a conflict before finality reopens even a "done" saga.
Detect(i) ==
    /\ ~final
    /\ Conflict(seen[i])
    /\ st[i] \in {"run", "done"}
    /\ st' = [st EXCEPT ![i] = "comp"]
    /\ UNCHANGED <<heads, seen, pos, outcome, applied, undone, final>>

Compensate(i) ==
    LET P == applied[i] \ undone[i] IN
    /\ st[i] = "comp"
    /\ IF P = {}
          THEN st' = [st EXCEPT ![i] = "aborted"] /\ UNCHANGED undone
          ELSE undone' = [undone EXCEPT ![i] = @ \cup {Max(P)}] /\ UNCHANGED st
    /\ UNCHANGED <<heads, seen, pos, outcome, applied, final>>

\* Finality deadline. Guard = partial synchrony: a full gossip round has
\* completed and every org has reacted to what it learned.
Finalize ==
    /\ ~final
    /\ \A i, j \in Orgs : seen[i] = seen[j]
    /\ \A i \in Orgs : st[i] \in {"done", "aborted"}
    /\ \A i \in Orgs : Conflict(seen[i]) => st[i] = "aborted"
    /\ final' = TRUE
    /\ UNCHANGED <<heads, seen, pos, st, outcome, applied, undone>>

Stutter == final /\ UNCHANGED vars

Next ==
    \/ \E i \in Orgs, p \in Phases, o \in Outcomes : OpByz /\ Issue(i, p, o)
    \/ \E i \in Orgs : HonestServe(i) \/ Proceed(i) \/ Timeout(i)
                       \/ Detect(i) \/ Compensate(i)
    \/ \E i, j \in Orgs : Gossip(i, j)
    \/ Finalize
    \/ Stutter

Fairness ==
    /\ \A i \in Orgs : /\ WF_vars(HonestServe(i)) /\ WF_vars(Proceed(i))
                       /\ WF_vars(Timeout(i))     /\ WF_vars(Detect(i))
                       /\ WF_vars(Compensate(i))
    /\ \A i, j \in Orgs : WF_vars(Gossip(i, j))
    /\ WF_vars(Finalize)

Spec     == Init /\ [][Next]_vars
FairSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
    /\ \A i \in Orgs : st[i] \in {"run", "done", "comp", "aborted"}
    /\ \A i \in Orgs : applied[i] \subseteq Phases /\ undone[i] \subseteq applied[i]
    /\ final \in BOOLEAN

\* A fork proof never exists against an honest operator.
ForkAccuracy == Fork(heads) => OpByz

\* Divergence is always visible: if two orgs acted on different outcomes for
\* a phase, the material they hold between them shows a conflict.
DivergenceDetectable ==
    \A i, j \in Orgs, p \in Phases :
        (outcome[i][p] = "commit" /\ outcome[j][p] = "abort")
            => Conflict(seen[i] \cup seen[j])

\* After finality every org reached the same outcome...
FinalAgreement == final => \A i, j \in Orgs : st[i] = st[j]

\* ...and an aborted saga is fully compensated.
FinalClean == final => \A i \in Orgs : st[i] = "aborted" => undone[i] = applied[i]

\* After finality, outcomes never change, whatever the operator signs later.
FinalStable == [][final => UNCHANGED <<st, applied, undone>>]_vars

\* The saga always reaches finality, even with a Byzantine operator.
Termination == <>final

-----------------------------------------------------------------------------
(* Non-vacuity witnesses: EXPECTED to be violated (with OpByz = TRUE). *)

NoForkEver        == ~Fork(heads)
NoReopenedSaga    == ~\E i \in Orgs : st[i] = "aborted" /\ applied[i] = Phases
NoPostFinalFork   == ~(final /\ Fork(heads) /\ \A i \in Orgs : st[i] = "done")
NoWithholding     == ~\E i \in Orgs, p \in Phases : Claim(i, p) \in seen[i]

=============================================================================
