package merkle

import (
	"fmt"
	"testing"
)

func leaves(n int) []Hash {
	out := make([]Hash, n)
	for i := range out {
		out[i] = LeafHash([]byte(fmt.Sprintf("leaf-%d", i)))
	}
	return out
}

func TestInclusionAllSizes(t *testing.T) {
	for n := 1; n <= 40; n++ {
		d := leaves(n)
		root := Root(d)
		for i := 0; i < n; i++ {
			p, err := InclusionProof(uint64(i), d)
			if err != nil {
				t.Fatal(err)
			}
			if !VerifyInclusion(uint64(i), uint64(n), d[i], p, root) {
				t.Fatalf("inclusion n=%d i=%d failed", n, i)
			}
			bad := LeafHash([]byte("tampered"))
			if VerifyInclusion(uint64(i), uint64(n), bad, p, root) {
				t.Fatalf("tampered leaf accepted n=%d i=%d", n, i)
			}
		}
	}
}

func TestConsistencyAllSizes(t *testing.T) {
	for n := 1; n <= 40; n++ {
		d := leaves(n)
		for m := 1; m <= n; m++ {
			p, err := ConsistencyProof(uint64(m), d)
			if err != nil {
				t.Fatal(err)
			}
			if !VerifyConsistency(uint64(m), uint64(n), Root(d[:m]), Root(d), p) {
				t.Fatalf("consistency m=%d n=%d failed", m, n)
			}
			// A forked history with the same size must not verify.
			forked := append([]Hash{}, d[:m]...)
			forked[m-1] = LeafHash([]byte("fork"))
			if m < n && VerifyConsistency(uint64(m), uint64(n), Root(forked), Root(d), p) {
				t.Fatalf("forked prefix accepted m=%d n=%d", m, n)
			}
		}
	}
}
