# Accountable Replicated Saga (ARS) — TLA+ models v3.1

A protocol for multi-step workflows that span mutually distrusting
organizations, such as AI agents from different companies transacting with each other.
Any number of orgs may be Byzantine. ARS doesn't try to *prevent*
misbehavior. It guarantees:

- **Accountability.** Every failure is pinned on a Byzantine party by
  public signed evidence. An honest party is never blamed.
- **Termination.** No party can stall a saga.
- **Consequences.** Blamed parties lose a posted bond.

Two specs:

| Spec | What it models |
|---|---|
| `AccountableSaga.tla` | The protocol: DAG-shaped sagas, replicated plans, owner/beneficiary side effects, trusted oracles, compensation, bond settlement. Assumes a consistent shared log. |
| `LogFork.tla` | Discharges that assumption. A log operator that shows orgs different histories is caught by gossip of signed heads, and in-flight sagas converge before finality. |

| `MCCheckout.tla` | A concrete instance: an AI shopping agent buying from a merchant's agent, with a payment processor as oracle and a carrier. |
| `AccountableSagaProofs.tla` | A TLAPS proof that honest orgs are never blamed, for **any** number of orgs, steps and Byzantine parties. |

Earlier versions are kept in `history/v1`, `history/v2` and `history/v3`. The mutated specs used for mutation testing are in `mutations/` (run each with `S.cfg`).

## v3.1: split response windows

The Go prototype's randomized test found a gap between the model and
anything you could actually implement. With one effect window, a Byzantine owner can
attest at the last instant. An honest beneficiary then has no time to
answer and is accused of being a *silent beneficiary*. v3 didn't show this
because its deadline actions *waited* for honest orgs, and no fixed-length
deadline can do that.

The fix is to never ask a party to respond inside the same window that its
counterparty controls:

- **Effect phase** = `effect` (the owner attests) + `respond` (the beneficiary confirms or disputes)
- **Compensation** = `open` (undos and receipts) + `respond` (beneficiaries check undos)
- **Oracle steps:** the beneficiary has no duty at all, because the oracle decides.

Every deadline guard now waits only for honest actions that were already
possible when its window opened, which a fixed-length window can guarantee.

## What changed in v3

| Open in v2 | v3 fix |
|---|---|
| Log equivocation assumed away | **Gossiped signed heads** (`LogFork.tla`). Two heads for one phase = fork proof against the operator. A withheld head = local timeout + gossiped claim. Any conflict before finality triggers **abort dominance**: everyone compensates. After finality, outcomes never change. |
| Disputes resolved externally | **Trusted per-step oracles.** On steps with an oracle (e.g. a payment processor's signed webhook), the oracle's report decides. False attestations and false disputes become **individual** evidence instead of a disputed pair. |
| No consequences | **Bonds.** At settlement, accused orgs are slashed, orgs in an unresolved dispute are frozen, everyone else gets their bond back. |
| Linear sagas only | **DAG sagas.** Steps open when their dependencies commit and run in parallel. Any abort cancels everything in flight. Compensation runs in reverse topological order. |

## Protocol (per step)

1. **Opens** once every step in `Deps[s]` has committed.
2. **Plan.** Every org re-executes the deterministic plan and logs a signed
   vote: the result, or `ABORT` if execution fails. At the deadline, the plan
   passes only if all votes match and nothing conflicts.
3. **Effect.** The **owner** performs the side effect and attests to it. On oracle
   steps the **oracle's** report decides. Otherwise the **beneficiary**
   confirms or disputes it. Deadline: commit or abort.
4. **Any abort aborts the saga.** Steps still in flight are cancelled. During the
   compensation window, orgs undo committed steps in reverse topological order and
   log receipts. Owners undo attested effects, including those of cancelled
   steps. The beneficiary or oracle checks each undo.
5. **Settlement** on bonds: slash, freeze or return.

### Evidence

| Evidence | Blames | Proof |
|---|---|---|
| Equivocation | one org | Two contradicting signed entries |
| Wrong result / unjustified veto | one org | Re-execution contradicts the vote |
| Silent voter, owner or beneficiary | one org | Deadline passed without its entry |
| False attestation / false undo | one org | Oracle never saw the effect or undo |
| False dispute | one org | Oracle saw what it disputed |
| Default | one org | Compensation deadline passed with an obligation unmet |
| Dispute (no oracle) | a pair | Beneficiary contradicts owner, and nothing settles it |
| Log fork | log operator | Two signed heads for one phase |

## Properties

**`AccountableSaga.tla`**

| Property | Meaning |
|---|---|
| `Accuracy` | No individual evidence names an honest org |
| `DisputeAccuracy` | Every unresolved dispute involves a Byzantine org |
| `AbortAccountability` | Every abort of a step that should have succeeded is attributable |
| `OracleAbortsNamed` | On oracle steps, blame is always individual, never a pair |
| `Validity` | A committed plan result is the correct, re-executable one |
| `EffectIntegrity` | A committed effect really happened (honest beneficiary or oracle) |
| `EffectsUndoneOrBlamed` | After compensation, every attested effect is undone or someone is blamed |
| `HonestReceiptsTruthful`, `HonestUndoOkTruthful` | Honest attestations never lie |
| `DepOrder` | A step opens only after all its dependencies committed |
| `CompensationReverseTopo` | A step is undone only after everything that depended on it |
| `HonestNeverSlashed` | Honest bonds are never slashed |
| `FrozenOnlyWithByz` | An honest bond is frozen only in a dispute with a Byzantine org |
| `SettlementStable` | No evidence appears after settlement; slashed ⇔ accused |
| `Termination` | Every saga finishes **and settles**, even with silent Byzantine orgs |

**`LogFork.tla`**

| Property | Meaning |
|---|---|
| `ForkAccuracy` | An honest operator never produces a fork proof |
| `DivergenceDetectable` | If two orgs acted on different outcomes for a phase, their combined material shows the conflict |
| `FinalAgreement` | After finality, every org reached the same outcome |
| `FinalClean` | A finally aborted saga is fully compensated |
| `FinalStable` | After finality, nothing an operator signs changes any outcome |
| `Termination` | Finality is always reached, even with a Byzantine operator |

## Model-checking results

TLC, v3.1 spec. "Holds" = every invariant listed above, plus `Termination` where marked.

**Core models** (3 orgs `a`, `b`, `c`; `c` Byzantine unless noted):

| Config | DAG | Result | Distinct states |
|---|---|---|---|
| `Full1Byz` | diamond (1 ∥ 2 → 3), oracle on Byzantine beneficiary's step | holds + termination | 510,564 |
| `OracleByzOwner` | diamond, oracle on Byzantine owner's step | holds + termination | 173,047 |
| `Chain1Byz` | 1 → 2, ∥ 3 | holds + termination | 2,345,668 |
| `FullHonest` | diamond, no Byzantine orgs | holds + termination | 1,995 |
| `LogForkByzOp` / `LogForkHonestOp` | log operator lying / honest | holds + termination + `FinalStable` | 44,302 / 95 |

**Checkout instance** (`MCCheckout.tla`: buyer, merchant, carrier, PSP oracle; lock → pay ∥ reserve → ship):

| Config | Result | Distinct states |
|---|---|---|
| `Checkout_Honest` | holds + termination | 7,986 |
| `Checkout_Byz_merchant` | holds (complete) | 1,896,087 |
| `Checkout_Byz_buyer` | no violation in a 50-min bounded run (incomplete; covered for all sizes by the TLAPS proof of `Accuracy`) | 16,604,644 |
| `Checkout_Byz_carrier` | holds (complete) | 1,151,026 |

**Witnesses** (all reachable, so no pass is vacuous): full completion, parallel steps, an
attested effect of a cancelled step being undone, the oracle catching a liar, an
unresolved dispute, slashing, freezing; for logs: a fork, a fork reopening a "done"
saga before finality, a fork after finality (with no effect), withholding.

**Mutations** show the properties actually catch bugs. Each one removes one
protocol rule, and TLC finds the expected violation:

| Mutation | Violation found |
|---|---|
| Effect deadline doesn't wait for the oracle | `Accuracy`: an honest owner is accused of a false attestation |
| Settle before the saga finishes | `SettlementStable`: evidence appears after bonds are settled |
| Compensate in any order (chain DAG) | `CompensationReverseTopo` |
| Finalize with an unresolved log conflict | `FinalAgreement` |

Run any config:

```sh
java -cp tla2tools.jar tlc2.TLC -workers auto -config Full1Byz.cfg MC.tla
java -cp tla2tools.jar tlc2.TLC -workers auto -config Checkout_Byz_merchant.cfg MCCheckout.tla
java -cp tla2tools.jar tlc2.TLC -workers auto -config LogForkByzOp.cfg LogFork.tla
```

Model instances:
- `MC.tla`: a diamond, where steps 1 ∥ 2 then 3. Oracle on step 1, where the Byzantine org is beneficiary.
- `MCOracleByzOwner.tla`: the same diamond, with the oracle on step 2, where the Byzantine org is owner.
- `MCChain.tla`: 1 → 2, in parallel with 3. Exercises reverse-topological undo.

## Proof: honest orgs are never blamed, at any size

TLC only checks small instances. `AccountableSagaProofs.tla` is a
machine-checked TLAPS proof of

```
THEOREM SpecAccuracy == Spec => []Accuracy
```

It holds for **any** number of orgs, Byzantine orgs, steps, plan values and any
DAG. TLAPS 1.6.0-pre proves all 1,633 obligations, with no omitted steps.

The proof uses an inductive invariant with twelve clauses, each closing one way
an honest org could otherwise be named by evidence:

| Clause | Says |
|---|---|
| I1 | Honest votes always equal the correct re-execution |
| I2 | Honest beneficiaries never contradict themselves, and never dispute on oracle steps |
| I3 | Once a plan closes, every honest org has voted |
| I4 | Once the owner window closes, an honest owner has attested |
| I5 | Once the effect phase ends, an honest beneficiary has answered |
| I6 | An honest owner only attests effects it really performed |
| I7 | The oracle reported every real effect before its phase ended |
| I8 | Nothing is undone before compensation starts |
| I9 | Compensation starts only with no step in flight |
| I10 | An honest owner's undo attestation is true |
| I11 | After the undo window, honest receipts and undos are all in |
| I12 | After compensation, honest undo checks and oracle refund reports are all in |

Structure:
- `InitInv`: the invariant holds initially.
- `Step_<Action>`: one lemma per action shows it preserves every clause.
- `Inductive` combines the step lemmas.
- `InvAccuracy` shows that none of the nine evidence predicates can name an honest org.
- `SpecAccuracy` closes with temporal logic.

Before the proof was attempted, TLC confirmed the invariant on 510k reachable states (`MCInv.tla`, `Inv1Byz.cfg`; TLC needs `TLAPS.tla` from your tlapm install on its library path, e.g. `-DTLA-Library=<tlapm>/lib/tlapm/stdlib`).

```sh
tlapm -I <tlapm>/lib/tlapm/stdlib AccountableSagaProofs.tla
```

`FinalAgreement` (in `LogFork.tla`) is still TLC-checked only. Proving it
needs reasoning about gossip convergence, which is a larger invariant.

## Assumptions

1. **Partial synchrony.** Deadlines are long enough for honest orgs, the
   oracle and one full gossip round. The mutations show this is
   load-bearing: break it and honest parties get blamed.
2. **Deterministic plans.** Only the plan half of a step is re-executed.
3. **An observer per effect.** A beneficiary that can see the effect, or a
   trusted oracle. Steps with neither rest on the owner's signed word.
4. **Trusted oracles are trusted.** A lying oracle is outside the guarantee.
   Use oracles that are already the source of truth, such as the payment processor.
5. **Withholding by the log operator is detectable, not provable.** It
   causes a clean abort, not blame. Equivocation is provable.
6. **Bond sizing is economic, not formal.** Slashing deters only when the bond is at least
   what a party could gain by misbehaving in one saga. A frozen bond needs an
   external resolution path.

## Not yet checked

- `Safety2Byz.cfg` (two Byzantine orgs, safety only) and
  `Checkout_Live_merchant.cfg` (checkout termination with a Byzantine merchant)
  haven't been run on v3.1. On a 2-core machine they exceed an hour. The
  TLAPS proof of `Accuracy` covers any number of Byzantine orgs.
- `Checkout_Byz_buyer.cfg` was only run as a bounded check (50 minutes,
  16.6M states, no violation).

## Open work

- A TLAPS proof of `FinalAgreement` (`LogFork.tla`), plus liveness proofs.
- Refinement: show the Go evaluator (`protocol.Evaluate`) implements the
  spec, for example with trace validation against TLC.
