package sim

import (
	"math/rand"
	"slices"
	"testing"
	"time"

	"github.com/AlfonsoCampodonico/ars/protocol"
)

func TestScenarios(t *testing.T) {
	for _, sc := range Scenarios() {
		t.Run(sc.Name, func(t *testing.T) {
			w := sc.Build()
			st := w.Run(6 * time.Hour)
			if !st.Finished {
				t.Fatalf("saga did not finish:\n%s", trace(w))
			}
			var accused []string
			for o := range st.Accused() {
				accused = append(accused, o)
			}
			slices.Sort(accused)
			want := slices.Clone(sc.Accused)
			slices.Sort(want)
			if !slices.Equal(accused, want) {
				t.Errorf("accused = %v, want %v\nevidence: %+v\n%s", accused, want, st.Evidence, trace(w))
			}
			for o, b := range sc.Bonds {
				if st.Bonds[o] != b {
					t.Errorf("bond[%s] = %s, want %s", o, st.Bonds[o], b)
				}
			}
			if card := w.Observed(StepPay); card != sc.Card {
				t.Errorf("buyer's card = %s, want %s", card, sc.Card)
			}
			var censored []string
			for _, c := range st.Censored {
				censored = append(censored, c.From)
			}
			if !slices.Equal(censored, sc.Censored) {
				t.Errorf("censored = %v, want %v", censored, sc.Censored)
			}
			if blamed := len(st.Operator) > 0; blamed != sc.OperatorBlamed {
				t.Errorf("operator blamed = %v, want %v: %+v", blamed, sc.OperatorBlamed, st.Operator)
			}
		})
	}
}

func trace(w *World) string {
	s := ""
	for _, l := range w.Trace {
		s += l + "\n"
	}
	return s
}

// TestRandomByzantineAccuracy mirrors the TLA+ properties Accuracy,
// DisputeAccuracy, EffectIntegrity and Termination: one random org behaves
// arbitrarily (random signed entries at random times, false censorship
// claims, random real-world effects); the others run honest sidecars and
// agents. Honest orgs must never be accused, every dispute must involve the
// Byzantine org, and the saga must always finish.
func TestRandomByzantineAccuracy(t *testing.T) {
	runs := 300
	if testing.Short() {
		runs = 40
	}
	for seed := int64(0); seed < int64(runs); seed++ {
		rng := rand.New(rand.NewSource(seed))
		w := randomWorld(rng)
		byz := []string{Buyer, Merchant, Carrier}[rng.Intn(3)]
		byzantine(w, rng, byz)
		st := w.Run(12 * time.Hour)
		checkRun(t, seed, w, st, byz)
		for _, c := range st.Censored {
			if c.From != byz {
				t.Fatalf("seed %d: honest operator, yet %s claims censorship", seed, c.From)
			}
		}
		if len(st.Operator) > 0 {
			t.Fatalf("seed %d: honest operator blamed: %+v", seed, st.Operator)
		}
	}
}

// TestRandomCensoringOperator mirrors the same properties with a log
// operator that refuses random entries, or signs receipts for them and drops
// them. Half the runs also have a Byzantine org. Censorship may abort a saga
// but must never get an honest org slashed, and an honest org's bond is
// frozen only for a claim of its own or a dispute with the Byzantine org.
func TestRandomCensoringOperator(t *testing.T) {
	runs := 200
	if testing.Short() {
		runs = 30
	}
	var censored, broken int
	for seed := int64(0); seed < int64(runs); seed++ {
		rng := rand.New(rand.NewSource(1000 + seed))
		w := randomWorld(rng)
		byz := ""
		if rng.Intn(2) == 0 {
			byz = []string{Buyer, Merchant, Carrier}[rng.Intn(3)]
			byzantine(w, rng, byz)
		}
		p := rng.Float64() * 0.15
		w.CensorLog(func(protocol.Entry) string {
			switch x := rng.Float64(); {
			case x < p/2:
				return "refuse"
			case x < p:
				return "drop"
			}
			return ""
		})
		st := w.Run(12 * time.Hour)
		checkRun(t, seed, w, st, byz)
		if len(st.Censored) > 0 {
			censored++
		}
		if len(st.Operator) > 0 {
			broken++
		}
		for o, b := range st.Bonds {
			if o == byz || b != protocol.BondFrozen {
				continue
			}
			ok := false
			for _, c := range st.Censored {
				ok = ok || c.From == o
			}
			for _, d := range st.Disputes {
				ok = ok || (d.Owner == o || d.Benef == o) && (d.Owner == byz || d.Benef == byz)
			}
			if !ok {
				t.Fatalf("seed %d: honest %s frozen without a claim or a Byzantine counterparty\n%s", seed, o, trace(w))
			}
		}
	}
	t.Logf("%d runs: %d with censorship claims, %d with a broken receipt", runs, censored, broken)
	if censored == 0 || broken == 0 {
		t.Fatal("the operator never misbehaved; the test proves nothing")
	}
}

func randomWorld(rng *rand.Rand) *World {
	terms := CheckoutTerms()
	if rng.Intn(4) == 0 {
		terms.ShipTo = "" // sometimes a justified abort
	}
	return NewWorld(terms)
}

// byzantine makes org byz behave arbitrarily.
func byzantine(w *World, rng *rand.Rand, byz string) {
	kinds := []protocol.Kind{protocol.KVote, protocol.KEffect, protocol.KConfirm, protocol.KDispute,
		protocol.KReceipt, protocol.KUndo, protocol.KUndoOk, protocol.KUndoDispute}
	p := 0.05 + rng.Float64()*0.4
	w.Org(byz).Agent.Raw = func(w *World, o *Org) {
		if rng.Float64() < 0.3 { // sometimes behave like a normal sidecar this tick
			todos, _ := o.Car.Tick()
			for _, td := range todos {
				if rng.Float64() < 0.7 {
					Honest(w, o, td)
				}
			}
		}
		for rng.Float64() < p {
			step := rng.Intn(len(w.Def.Steps))
			e := protocol.Entry{Kind: kinds[rng.Intn(len(kinds))], Step: step}
			if e.Kind == protocol.KVote {
				e.Val = []string{w.State().Steps[step].Truth, protocol.Abort, "deadbeef"}[rng.Intn(3)]
			}
			if rng.Intn(4) == 0 {
				w.Claim(byz, e) // "the operator refused it"
			} else {
				w.Post(byz, e)
			}
		}
		for step, sd := range w.Def.Steps {
			if sd.Owner == byz && rng.Float64() < p/3 {
				if w.Real[step] == "no" {
					w.DoEffect(step)
				} else {
					w.UndoEffect(step)
				}
			}
		}
	}
}

// checkRun asserts Accuracy, DisputeAccuracy, EffectIntegrity,
// HonestNeverSlashed and Termination for one run with Byzantine org byz
// ("" for none).
func checkRun(t *testing.T, seed int64, w *World, st *protocol.State, byz string) {
	t.Helper()
	if !st.Finished {
		t.Fatalf("seed %d: saga did not finish (byz=%s)", seed, byz)
	}
	for o := range st.Accused() {
		if o != byz {
			t.Fatalf("seed %d: honest %s accused (byz=%s): %+v\n%s", seed, o, byz, st.Evidence, trace(w))
		}
	}
	for _, d := range st.Disputes {
		if d.Owner != byz && d.Benef != byz {
			t.Fatalf("seed %d: dispute between honest orgs %+v", seed, d)
		}
	}
	for i, s := range st.Steps {
		b := w.Def.Steps[i].Benef
		if s.Stage == protocol.Committed && (b != byz || w.Def.Steps[i].Oracle != "") && w.Real[i] == "no" {
			t.Fatalf("seed %d: step %d committed but its effect never happened", seed, i)
		}
	}
	for o, b := range st.Bonds {
		if o != byz && b == protocol.BondSlashed {
			t.Fatalf("seed %d: honest %s slashed", seed, o)
		}
	}
}
