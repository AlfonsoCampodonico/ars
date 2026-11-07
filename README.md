# ARS — Accountable Replicated Saga

A protocol for multi-step workflows (sagas) across organizations that don't
trust each other, such as AI agents from different companies transacting.
Any party may be Byzantine. ARS doesn't try to *prevent* misbehavior; it
guarantees:

- **Accountability.** Every failure is pinned on a misbehaving party by
  public, signed evidence. An honest party is never blamed.
- **Termination.** No party can stall a saga.
- **Consequences.** Blamed parties lose a posted bond.

This repo has the TLA+ specification (model-checked, with a machine-checked
TLAPS proof that honest parties are never blamed) and a Go prototype.

## Repository layout

| Path | Contents |
|---|---|
| `spec/` | TLA+ specs, model configs, the TLAPS proof, and the [spec README](spec/README.md) with design and results |
| `spec/history/` | Earlier spec versions (v1–v3) |
| `spec/mutations/` | Deliberately broken specs, used to show the properties catch bugs |
| `merkle/`, `translog/` | RFC 9162 Merkle tree and the transparency log |
| `protocol/` | Entries, saga definitions, deterministic plans, `Evaluate` |
| `sidecar/`, `oracle/` | Per-org runtime; mock payment processor |
| `sim/` | Simulation harness, scenarios, randomized Byzantine tests |
| `cmd/` | `arslog` (log server), `arsd` (sidecar + MCP server), `demo` |

## Verification status

| What | How | Result |
|---|---|---|
| Honest parties are never blamed (`Accuracy`) | TLAPS, for all sizes | Proved (1,633 obligations) |
| All 15 safety invariants + termination | TLC, diamond and chain DAGs, 1 Byzantine org | Hold (up to 2.3M states) |
| Checkout instance | TLC, honest / Byzantine merchant / Byzantine carrier | Hold (up to 1.9M states) |
| Log forks: detection, agreement after finality | TLC, `LogFork.tla` | Hold |
| Properties are not vacuous | 11 witness configs | All scenarios reachable |
| Properties catch bugs | 4 mutated specs | All caught |
| Go implementation | 300 randomized Byzantine runs | `Accuracy`, `DisputeAccuracy`, `EffectIntegrity`, termination hold |

See [spec/README.md](spec/README.md) for details and what hasn't been checked yet.


A Go prototype of the ARS protocol from the TLA+ specs. AI agents from
different companies run a multi-step deal, here a checkout. No one has to
trust anyone else: every statement is signed and stored on a transparency log,
every step can be re-executed by every party, and whoever misbehaves
leaves public evidence and loses a bond.

```
 buyer agent        merchant agent        carrier agent          payment processor
      │ MCP               │ MCP                 │ MCP                    │ (oracle)
 ┌────▼─────┐       ┌─────▼────┐          ┌─────▼────┐                   │
 │  arsd    │       │  arsd    │          │  arsd    │   signed reports  │
 │ sidecar  │       │ sidecar  │          │ sidecar  │◄──────────────────┘
 └────┬─────┘       └────┬─────┘          └────┬─────┘
      │  signed entries  │                     │
      └──────────────────┼─────────────────────┘
                   ┌─────▼──────┐    signed tree heads, gossiped
                   │   arslog   │──► between sidecars to catch forks
                   └────────────┘
```

## Design rules

- **The LLM never signs.** Each org's sidecar (`arsd`) holds the key. It
  re-executes every plan and votes by itself; the agent cannot choose a
  vote. The agent can only report facts through four MCP tools:
  `attest_effect`, `observe_effect`, `attest_undo`, `observe_undo`. Each one is
  checked against the org's role and the current phase, and an org can
  never contradict itself.
- **Everything is a pure function of the log.** `protocol.Evaluate(def,
  log, now)` derives every step's stage, the abort point, compensation
  obligations, evidence and bond settlement. Every org computes the same
  answer, so nobody needs to agree on anything beyond the log itself.
- **Deadlines, not waiting.** Each step has a plan window, an owner window,
  and a beneficiary window. A party that goes silent causes an abort
  plus evidence; it can never stall the saga.

## Checkout saga

| # | Step | Plan (re-executed by all) | Owner → beneficiary | Oracle |
|---|---|---|---|---|
| 0 | lock terms | price, tax, total, buyer's spend limit | merchant → buyer | — |
| 1 | pay | amount + currency | merchant (captures) → buyer | PSP |
| 2 | reserve | stock + pickup slot | merchant → carrier | — |
| 3 | ship | manifest + address | carrier → buyer | — |

Steps 1 and 2 run in parallel after 0; step 3 needs both. Suggested
production windows (the simulation compresses them):

| Window | Lock | Pay | Reserve | Ship | Compensation |
|---|---|---|---|---|---|
| Plan (all vote) | 2 min | 2 min | 2 min | 2 min | — |
| Owner (attest) | 10 min | 15 min | 1 h | 5 days | 3 days (refund, cancel) |
| Beneficiary (respond) | 10 min | — (oracle decides) | 1 h | 2 days | 2 days |

## Try it

Requires Go 1.25+ (and Java 11+ for TLC).

```sh
make test                          # go vet + all tests, incl. 300 random Byzantine runs
make tlc-quick                     # downloads tla2tools.jar, runs the fast TLC configs
make tlaps                         # needs tlapm installed (TLAPM=/path/to/tlapm)
go run ./cmd/demo                  # all scenarios
go run ./cmd/demo -scenario carrier-lies -v
go run ./cmd/demo -fork            # equivocating log operator -> fork proof
```

Run it for real with an MCP client:

```sh
go run ./cmd/demo -example ./example        # saga.json + keys (saga starts in 1 min)
go run ./cmd/arslog -addr :8070 -key example/log.key
# in your MCP client config, one server per org:
#   arsd -def example/saga.json -org merchant -key example/merchant.key -log http://localhost:8070
```

## Scenarios

| Scenario | What happens | Outcome |
|---|---|---|
| `happy` | Everyone behaves | All committed, bonds returned |
| `tampered-merchant` | Merchant software adds a hidden €18 fee | Its vote doesn't match re-execution → abort at step 0, merchant slashed |
| `fake-capture` | Merchant claims a capture it never made | PSP never reports it → merchant slashed, order unwound |
| `carrier-lies` | Carrier claims delivery; buyer disputes | No oracle for delivery → carrier and buyer bonds frozen pending resolution; buyer refunded |
| `undeliverable` | No address → ship plan fails for everyone | Justified abort, full refund, nobody blamed |
| `refund-dodger` | As above, but merchant fakes the refund | PSP never reports it → merchant slashed |
| `carrier-vanishes` | Carrier goes offline mid-saga | Deadlines pass → abort, refund, carrier slashed |

## Tests that mirror the spec

`TestRandomByzantineAccuracy` runs 300 sagas. In each one, a random org
behaves arbitrarily: it signs random entries at random times and performs or
undoes real effects at random. The other orgs run honest sidecars. The test checks the
spec's `Accuracy`, `DisputeAccuracy`, `EffectIntegrity`, `HonestNeverSlashed`
and `Termination` on every run.

This test found a real gap in the spec (fixed in v3.1). With a single
effect window, a Byzantine owner that attests at the last instant leaves an
honest beneficiary no time to answer, and the beneficiary gets accused of being silent. The TLA+
model hid it because its deadline action waited for honest orgs to act,
which no fixed-length deadline can guarantee. Effect and compensation phases
are now split into an owner window and a beneficiary window.

## Not in the prototype yet

- Persistence. The log and sidecars are in-memory, and the log has no witness
  cosigning.
- Abort dominance on log forks (`LogFork.tla`). The prototype detects and
  proves forks, but doesn't yet roll back sagas on detection.
- Real bonds/escrow. Settlement is computed, not enforced.
- Authentication on the log's HTTP API, rate limits, and entry size checks
  beyond 1 MiB.

## License

Apache-2.0. See [LICENSE](LICENSE).
