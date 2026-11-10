#!/usr/bin/env python3
"""Regenerate the step lemmas of AccountableSagaProofs.tla.

The inductive step is one lemma per action of AccountableSaga.tla and one
goal per clause of Inv, each closed by the backends from definitions. This
script rewrites everything between the base case and THEOREM Inductive;
the invariant, the base case and the closing theorems are edited by hand.

    python3 gen_proofs.py          # rewrites AccountableSagaProofs.tla
    tlapm AccountableSagaProofs.tla

Add an action to ACTIONS when the spec gains one; add a (lemma, clause)
entry to HINTS when a single goal needs an extra fact."""
import os

CLAUSES = ["TypeInv"] + [f"I{i}" for i in range(1, 13)]

COMMON = ("Has, Signed, Filed, FiledVote, AttestFiled, UndoFiled, RespondFiled, "
          "UndoRespondFiled, OracleDoneFiled, OracleUndoneFiled, Claim, PlanClosed, Closed, "
          "PastAttest, EffDone, Attested, UndoAttested, BenefDue, UndoBenefDue, OwesReceipt, "
          "OwesUndo, Compensating, Entry, Vote, HonestVote, Honest, Abort")

# (lemma name, ASSUME hypotheses, defs to unfold for every goal)
ACTIONS = [
    ("HVote", "NEW i \\in Honest, HVote(i)", ["HVote", "Post"]),
    ("HEffect", "NEW i \\in Honest, HEffect(i)", ["HEffect", "Post", "I9"]),
    ("HRespond", "NEW i \\in Honest, HRespond(i)", ["HRespond", "Post"]),
    ("HCompensate", "NEW i \\in Honest, HCompensate(i)", ["HCompensate", "Post"]),
    ("HUndo", "NEW i \\in Honest, HUndo(i)", ["HUndo", "Post", "I6", "I9"]),
    ("HUndoRespond", "NEW i \\in Honest, HUndoRespond(i)", ["HUndoRespond", "Post"]),
    ("OracleReport", "OracleReport", ["OracleReport", "Post"]),
    ("ClosePlan", "NEW s0 \\in Steps, ClosePlan(s0)", ["ClosePlan", "StartAbort", "EndAt", "Stages", "Bonds"]),
    ("CloseAttest", "NEW s0 \\in Steps, CloseAttest(s0)", ["CloseAttest", "Stages"]),
    ("CloseEffect", "NEW s0 \\in Steps, CloseEffect(s0)",
     ["CloseEffect", "StartAbort", "StartHold", "EndAt", "CommitStep", "EffectOK", "EffectDisputed",
      "Committed", "Stages", "Bonds", "I8", "I9"]),
    ("CloseUndo", "CloseUndo", ["CloseUndo"]),
    ("CloseComp", "CloseComp", ["CloseComp"]),
    ("Settle", "Settle", ["Settle", "Bonds"]),
    ("BVote", "BVote", ["BVote", "BPost"]),
    ("BPostEffectPhase", "BPostEffectPhase", ["BPostEffectPhase", "BPost", "I9"]),
    ("BPostCompPhase", "BPostCompPhase", ["BPostCompPhase", "BPost", "I9"]),
    ("BEffect", "BEffect", ["BEffect", "I8", "I9"]),
    ("Terminated", "Terminated", ["Terminated", "vars"]),
    ("UNCHANGEDvars", "UNCHANGED vars", ["vars"]),
]

# Extra per-goal hints: (action, clause) -> extra defs/facts.
HINTS = {
    ("CloseEffect", "I7"): ["I7"],
}

def lemma(name, params, defs):
    out = [f"LEMMA Step_{name} ==", f"  ASSUME Inv, {params}", "  PROVE Inv'",
           "<1> USE DEF Inv, TypeInv"]
    for n, cl in enumerate(CLAUSES, 1):
        d = [x for x in defs + HINTS.get((name, cl), []) if x != cl]
        out.append(f"<1>{n}. {cl}'")
        out.append(f"  BY OracleSub, PPStable, PPSame, SagaAssumptions DEF {', '.join(d)}, {cl}, {COMMON}")
    out.append("<1> QED BY " + ", ".join(f"<1>{n}" for n in range(1, len(CLAUSES) + 1)))
    return "\n".join(out) + "\n"

MARK_START = "(* Inductive step, one lemma per action. *)\n"
MARK_END = "THEOREM Inductive =="

path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "AccountableSagaProofs.tla")
text = open(path).read()
head, rest = text.split(MARK_START, 1)
tail = rest[rest.index(MARK_END):]
body = "\n".join(lemma(*a) for a in ACTIONS)
open(path, "w").write(head + MARK_START + body + "\n" + tail)
