package sim

import (
	"math/rand"
	"slices"
	"testing"
	"time"

	"ars/protocol"
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
			// Whatever happened, the buyer must not end up charged for an
			// aborted order (EffectsUndoneOrBlamed, from the buyer's view).
			if st.Aborted && w.Observed(StepPay) == "done" && !st.Accused()[Merchant] {
				t.Errorf("buyer still charged after abort and merchant not blamed")
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
// arbitrarily (random signed entries at random times, random real-world
// effects); the others run honest sidecars and agents. Honest orgs must
// never be accused, every dispute must involve the Byzantine org, and the
// saga must always finish.
func TestRandomByzantineAccuracy(t *testing.T) {
	kinds := []protocol.Kind{protocol.KVote, protocol.KEffect, protocol.KConfirm, protocol.KDispute,
		protocol.KReceipt, protocol.KUndo, protocol.KUndoOk, protocol.KUndoDispute}
	runs := 300
	if testing.Short() {
		runs = 40
	}
	for seed := int64(0); seed < int64(runs); seed++ {
		rng := rand.New(rand.NewSource(seed))
		terms := CheckoutTerms()
		if rng.Intn(4) == 0 {
			terms.ShipTo = "" // sometimes a justified abort
		}
		w := NewWorld(terms)
		byz := []string{Buyer, Merchant, Carrier}[rng.Intn(3)]
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
				w.Post(byz, e)
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
		st := w.Run(12 * time.Hour)
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
}
