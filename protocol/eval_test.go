package protocol_test

import (
	"encoding/json"
	"fmt"
	"math/rand"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/AlfonsoCampodonico/ars/protocol"
	"github.com/AlfonsoCampodonico/ars/sim"
	"github.com/AlfonsoCampodonico/ars/translog"
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

// A receipt from another log run by the same operator key proves nothing
// about this saga's log: the claim stays a plain censorship dispute.
func TestReceiptFromAnotherLogIsNotABrokenPromise(t *testing.T) {
	w := sim.NewWorld(sim.CheckoutTerms())
	other := translog.New("some-other-log", sim.Key(sim.LogOperator), w.Clock.Now)
	w.CensorLog(func(e protocol.Entry) string {
		if e.From == sim.Buyer && e.Kind == protocol.KVote && e.Step == sim.StepLock {
	w.Run(6 * time.Hour)
		}
		return ""
	})
	st := w.Run(6 * time.Hour)
	claims, _ := w.Gossip.Claims()
	if len(claims) != 1 {
		t.Fatalf("want one claim, got %d", len(claims))
	}
	data, _ := json.Marshal(claims[0].Entry)
	r := other.Promise(data)
	forged := protocol.Claim{Entry: claims[0].Entry, Time: claims[0].Time, Receipt: &r}.Sign(sim.Key(sim.Buyer))
	recs, _ := protocol.ReadRecords(w.Log)
	st, err := protocol.Evaluate(w.Def, protocol.CheckoutPlans(), recs, []protocol.Claim{forged}, w.Clock.Now())
	if err != nil {
		t.Fatal(err)
	}
	if len(st.Operator) != 0 || len(st.Censored) != 1 {
		t.Fatalf("foreign receipt accepted as proof: operator=%+v censored=%+v", st.Operator, st.Censored)
	}
}

// Junk in a shared gossip directory is skipped, not fatal.
func TestDirGossipSkipsJunk(t *testing.T) {
	dir := t.TempDir()
	g := protocol.DirGossip{Dir: dir}
	c := protocol.Claim{Entry: protocol.Entry{Saga: "s", Kind: protocol.KVote, From: "a", Val: "x"}}.Sign(sim.Key("a"))
	if err := g.Publish(c); err != nil {
		t.Fatal(err)
	}
	os.WriteFile(filepath.Join(dir, "garbage.json"), []byte("not json"), 0o644)
	os.Mkdir(filepath.Join(dir, "adir.json"), 0o755)
	os.WriteFile(filepath.Join(dir, "huge.json"), make([]byte, 2<<20), 0o644)
	os.Symlink("/etc/passwd", filepath.Join(dir, "link.json"))
	got, err := g.Claims()
	if err != nil || len(got) != 1 {
		t.Fatalf("want the one real claim, got %d claims, err %v", len(got), err)
	}
}
