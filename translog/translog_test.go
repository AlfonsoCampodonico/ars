package translog

import (
	"crypto/ed25519"
	"fmt"
	"net/http/httptest"
	"testing"

	"ars/merkle"
)

func newLog(t *testing.T) (*Log, ed25519.PublicKey) {
	pub, priv, err := ed25519.GenerateKey(nil)
	if err != nil {
		t.Fatal(err)
	}
	return New("test-log", priv, nil), pub
}

func TestProofsOverHTTP(t *testing.T) {
	l, pub := newLog(t)
	srv := httptest.NewServer(Handler(l))
	defer srv.Close()
	c := &Client{Base: srv.URL}
	var mid Checkpoint
	for i := 0; i < 13; i++ {
		if _, err := c.Append([]byte(fmt.Sprintf("e%d", i))); err != nil {
			t.Fatal(err)
		}
		if i == 4 {
			mid, _ = c.Latest()
		}
	}
	last, err := c.Latest()
	if err != nil || !last.Verify(pub) || last.Size != 13 {
		t.Fatalf("bad latest checkpoint: %+v %v", last, err)
	}
	if err := verifyExtends(c, mid, last); err != nil {
		t.Fatalf("consistency over HTTP: %v", err)
	}
	entries, _ := c.Entries(0)
	root, _ := decodeRoot(last.Root)
	for _, e := range entries {
		p, err := c.InclusionProof(e.Index, last.Size)
		if err != nil {
			t.Fatal(err)
		}
		if !merkle.VerifyInclusion(e.Index, last.Size, merkle.LeafHash(e.Bytes()), p, root) {
			t.Fatalf("inclusion of %d failed", e.Index)
		}
	}
}

func TestForkDetected(t *testing.T) {
	l, pub := newLog(t)
	l.Append([]byte("shared"))
	evil := l.Fork()
	l.Append([]byte("phase 3: commit"))
	evil.Append([]byte("phase 3: abort"))

	p, err := CompareViews(pub, l, evil)
	if err != nil {
		t.Fatal(err)
	}
	if p == nil || !p.Valid(pub) {
		t.Fatal("fork not detected")
	}

	// Honest views that are merely at different sizes are fine.
	l2, pub2 := newLog(t)
	l2.Append([]byte("a"))
	behind := l2.Fork() // same history, fewer entries
	l2.Append([]byte("b"))
	if p, err := CompareViews(pub2, l2, behind); err != nil || p != nil {
		t.Fatalf("false fork: %v %v", p, err)
	}
}
