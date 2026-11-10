package protocol

import (
	"crypto/ed25519"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sync"
	"time"

	"github.com/AlfonsoCampodonico/ars/translog"
)

// Claim says the log operator refused an entry, or accepted it and then
// didn't keep it. It travels by gossip between orgs, not on the log.
//
// Without a receipt a claim can't be proven: it discharges the claimant's
// duty and puts it in an unresolved dispute with the operator (its bond is
// frozen, not slashed). With a receipt the operator signed for the entry,
// a log that doesn't hold that leaf proves the operator broke its promise.
type Claim struct {
	Entry   Entry             `json:"entry"`
	Time    time.Time         `json:"time"` // when the claimant submitted the entry
	Receipt *translog.Receipt `json:"receipt,omitempty"`
	Sig     []byte            `json:"sig"` // by the entry's signer, over everything above
}

func (c Claim) signingBytes() []byte {
	c.Sig = nil
	b, _ := json.Marshal(c)
	return append([]byte("ars-claim-v1\n"), b...)
}

// Sign returns c signed with key, which must be the entry signer's.
func (c Claim) Sign(key ed25519.PrivateKey) Claim {
	c.Sig = ed25519.Sign(key, c.signingBytes())
	return c
}

// Verify checks the claimant's signature on the claim and on its entry.
func (c Claim) Verify(pub ed25519.PublicKey) bool {
	return len(pub) == ed25519.PublicKeySize && ed25519.Verify(pub, c.signingBytes(), c.Sig) && c.Entry.Verify(pub)
}

// Gossip carries claims between every party of a saga. Every org must see
// the same claims before the saga's outcome is final (see LogFork.tla).
type Gossip interface {
	Publish(Claim) error
	Claims() ([]Claim, error)
}

// Bus is an in-process Gossip shared by everyone in one process.
type Bus struct {
	mu     sync.Mutex
	claims []Claim
}

func (b *Bus) Publish(c Claim) error {
	b.mu.Lock()
	defer b.mu.Unlock()
	b.claims = append(b.claims, c)
	return nil
}

func (b *Bus) Claims() ([]Claim, error) {
	b.mu.Lock()
	defer b.mu.Unlock()
	return append([]Claim(nil), b.claims...), nil
}

// ReadRecords reads and decodes the whole log. Leaves that aren't entries
// are kept (with a zero Entry) so receipts can still be checked against them.
func ReadRecords(log translog.API) ([]Record, error) {
	leaves, err := log.Entries(0)
	if err != nil {
		return nil, err
	}
	out := make([]Record, 0, len(leaves))
	for _, l := range leaves {
		var e Entry
		_ = json.Unmarshal(l.Data, &e)
		out = append(out, Record{Entry: e, Time: l.Time, Index: l.Index, Leaf: translog.LeafHash(l)})
	}
	return out, nil
}

// Submitter signs entries for one party and puts them on the log. When the
// log refuses an entry, or later doesn't hold one it gave a receipt for,
// the submitter gossips a claim instead.
type Submitter struct {
	Saga   string
	From   string
	Key    ed25519.PrivateKey
	Log    translog.API
	LogKey ed25519.PublicKey
	Gossip Gossip
	Clock  func() time.Time

	mu      sync.Mutex
	sent    []sent
	claimed []Entry
}

type sent struct {
	entry   Entry
	at      time.Time
	receipt translog.Receipt
	claimed bool
}

func (s *Submitter) now() time.Time {
	if s.Clock != nil {
		return s.Clock()
	}
	return time.Now()
}

// Submit signs e and appends it to the log. A refused entry (an error, or a
// receipt that doesn't check out) is gossiped as a claim, which discharges
// the duty just the same.
func (s *Submitter) Submit(e Entry) error {
	e.Saga, e.From = s.Saga, s.From
	e = e.Sign(s.Key)
	b, err := json.Marshal(e)
	if err != nil {
		return err
	}
	at := s.now()
	r, err := s.Log.Append(b)
	if err == nil && r.Verify(s.LogKey) && r.For(b) {
		s.mu.Lock()
		s.sent = append(s.sent, sent{entry: e, at: at, receipt: r})
		s.mu.Unlock()
		return nil
	}
	return s.claim(e, at, nil)
}

// Audit checks every receipt against the log and gossips a claim, with the
// receipt as proof, for each entry the log no longer holds as promised.
func (s *Submitter) Audit(recs []Record) error {
	leaf := make(map[uint64]string, len(recs))
	for _, r := range recs {
		leaf[r.Index] = r.Leaf
	}
	s.mu.Lock()
	var broken []sent
	for i := range s.sent {
		if x := &s.sent[i]; !x.claimed && leaf[x.receipt.Index] != x.receipt.LeafHash {
			x.claimed = true
			broken = append(broken, *x)
		}
	}
	s.mu.Unlock()
	for _, x := range broken {
		if err := s.claim(x.entry, x.at, &x.receipt); err != nil {
			return err
		}
	}
	return nil
}

func (s *Submitter) claim(e Entry, at time.Time, r *translog.Receipt) error {
	c := Claim{Entry: e, Time: at, Receipt: r}.Sign(s.Key)
	if err := s.Gossip.Publish(c); err != nil {
		return fmt.Errorf("gossip claim: %w", err)
	}
	s.mu.Lock()
	s.claimed = append(s.claimed, e)
	s.mu.Unlock()
	return nil
}

// Claimed reports whether this party gossiped a claim for an entry of one
// of these kinds on step.
func (s *Submitter) Claimed(step int, kinds ...Kind) bool {
	s.mu.Lock()
	defer s.mu.Unlock()
	for _, e := range s.claimed {
		for _, k := range kinds {
			if e.Step == step && e.Kind == k {
				return true
			}
		}
	}
	return false
}

// DirGossip is a Gossip over a shared directory, one file per claim, for
// parties running as separate processes on one machine (or sharing a
// synced folder). A real deployment gossips over the network instead.
type DirGossip struct{ Dir string }

func (g DirGossip) Publish(c Claim) error {
	b, err := json.Marshal(c)
	if err != nil {
		return err
	}
	if err := os.MkdirAll(g.Dir, 0o755); err != nil {
		return err
	}
	h := sha256.Sum256(b)
	tmp := filepath.Join(g.Dir, ".tmp-"+hex.EncodeToString(h[:]))
	if err := os.WriteFile(tmp, b, 0o644); err != nil {
		return err
	}
	return os.Rename(tmp, filepath.Join(g.Dir, hex.EncodeToString(h[:])+".json"))
}

func (g DirGossip) Claims() ([]Claim, error) {
	files, err := filepath.Glob(filepath.Join(g.Dir, "*.json"))
	if err != nil {
		return nil, err
	}
	var out []Claim
	for _, f := range files {
		b, err := os.ReadFile(f)
		if err != nil {
			return nil, err
		}
		var c Claim
		if json.Unmarshal(b, &c) == nil {
			out = append(out, c)
		}
	}
	return out, nil
}
