package protocol_test

import (
	"fmt"
	"math/rand"
	"testing"
	"time"

	"github.com/AlfonsoCampodonico/ars/protocol"
	"github.com/AlfonsoCampodonico/ars/sim"
)

// Every org must reach the same verdict from the same claims, whatever
// order gossip delivered them in -- including duplicates, and a plain claim
// next to a receipt-backed one for the same entry.
func TestClaimOrderDoesNotMatter(t *testing.T) {
	var sc sim.Scenario
	for _, s := range sim.Scenarios() {
		if s.Name == "broken-promise" {
			sc = s
		}
	}
	w := sc.Build()
	w.Run(6 * time.Hour)
	claims, _ := w.Gossip.Claims()
	if len(claims) != 1 || claims[0].Receipt == nil {
		t.Fatalf("want one receipt-backed claim, got %+v", claims)
	}
	plain := protocol.Claim{Entry: claims[0].Entry, Time: claims[0].Time}.Sign(sim.Key(sim.Buyer))
	claims = append(claims, plain, claims[0], plain)

	recs, err := protocol.ReadRecords(w.Log)
	if err != nil {
		t.Fatal(err)
	}
	var want string
	rng := rand.New(rand.NewSource(1))
	for i := 0; i < 20; i++ {
		rng.Shuffle(len(claims), func(a, b int) { claims[a], claims[b] = claims[b], claims[a] })
		st, err := protocol.Evaluate(w.Def, protocol.CheckoutPlans(), recs, claims, w.Clock.Now())
		if err != nil {
			t.Fatal(err)
		}
		got := fmt.Sprint(st.Censored, st.Operator, st.Bonds)
		if i == 0 {
			want = got
			if len(st.Operator) != 1 || len(st.Censored) != 0 {
				t.Fatalf("want one broken promise and no censorship dispute, got %s", got)
			}
		}
		if got != want {
			t.Fatalf("verdict depends on claim order:\n%s\nvs\n%s", got, want)
		}
	}
}
