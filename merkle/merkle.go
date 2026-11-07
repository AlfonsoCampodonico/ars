// Package merkle implements RFC 9162 (Certificate Transparency v2) Merkle
// tree hashing, inclusion proofs and consistency proofs.
package merkle

import (
	"bytes"
	"crypto/sha256"
	"errors"
	"math/bits"
)

// Hash is a SHA-256 digest.
type Hash [32]byte

// LeafHash returns HASH(0x00 || data).
func LeafHash(data []byte) Hash {
	h := sha256.New()
	h.Write([]byte{0x00})
	h.Write(data)
	var out Hash
	copy(out[:], h.Sum(nil))
	return out
}

// NodeHash returns HASH(0x01 || l || r).
func NodeHash(l, r Hash) Hash {
	h := sha256.New()
	h.Write([]byte{0x01})
	h.Write(l[:])
	h.Write(r[:])
	var out Hash
	copy(out[:], h.Sum(nil))
	return out
}

// EmptyRoot is the root of the empty tree: HASH("").
func EmptyRoot() Hash { return sha256.Sum256(nil) }

// largestPow2Below returns the largest power of two strictly less than n (n >= 2).
func largestPow2Below(n uint64) uint64 {
	return uint64(1) << (bits.Len64(n-1) - 1)
}

// Root computes MTH over the given leaf hashes.
func Root(leaves []Hash) Hash {
	switch len(leaves) {
	case 0:
		return EmptyRoot()
	case 1:
		return leaves[0]
	}
	k := largestPow2Below(uint64(len(leaves)))
	return NodeHash(Root(leaves[:k]), Root(leaves[k:]))
}

// InclusionProof returns the audit path for leaf m in the tree of the given leaves.
func InclusionProof(m uint64, leaves []Hash) ([]Hash, error) {
	if m >= uint64(len(leaves)) {
		return nil, errors.New("merkle: leaf index out of range")
	}
	return inclusion(m, leaves), nil
}

func inclusion(m uint64, d []Hash) []Hash {
	n := uint64(len(d))
	if n <= 1 {
		return nil
	}
	k := largestPow2Below(n)
	if m < k {
		return append(inclusion(m, d[:k]), Root(d[k:]))
	}
	return append(inclusion(m-k, d[k:]), Root(d[:k]))
}

// ConsistencyProof proves the tree of size m is a prefix of the tree of all leaves.
func ConsistencyProof(m uint64, leaves []Hash) ([]Hash, error) {
	n := uint64(len(leaves))
	if m == 0 || m > n {
		return nil, errors.New("merkle: invalid consistency range")
	}
	return subproof(m, leaves, true), nil
}

func subproof(m uint64, d []Hash, b bool) []Hash {
	n := uint64(len(d))
	if m == n {
		if b {
			return nil
		}
		return []Hash{Root(d)}
	}
	k := largestPow2Below(n)
	if m <= k {
		return append(subproof(m, d[:k], b), Root(d[k:]))
	}
	return append(subproof(m-k, d[k:], false), Root(d[:k]))
}

// VerifyInclusion checks an audit path (RFC 9162 section 2.1.3.2).
func VerifyInclusion(index, size uint64, leaf Hash, path []Hash, root Hash) bool {
	if index >= size {
		return false
	}
	fn, sn := index, size-1
	r := leaf
	for _, p := range path {
		if sn == 0 {
			return false
		}
		if fn&1 == 1 || fn == sn {
			r = NodeHash(p, r)
			if fn&1 == 0 {
				for fn&1 == 0 && fn != 0 {
					fn >>= 1
					sn >>= 1
				}
			}
		} else {
			r = NodeHash(r, p)
		}
		fn >>= 1
		sn >>= 1
	}
	return sn == 0 && r == root
}

// VerifyConsistency checks a consistency proof (RFC 9162 section 2.1.4.2).
func VerifyConsistency(first, second uint64, firstRoot, secondRoot Hash, path []Hash) bool {
	switch {
	case first > second:
		return false
	case first == second:
		return len(path) == 0 && firstRoot == secondRoot
	case first == 0:
		return len(path) == 0
	}
	if len(path) == 0 {
		return false
	}
	if first&(first-1) == 0 { // exact power of two
		path = append([]Hash{firstRoot}, path...)
	}
	fn, sn := first-1, second-1
	for fn&1 == 1 {
		fn >>= 1
		sn >>= 1
	}
	fr, sr := path[0], path[0]
	for _, c := range path[1:] {
		if sn == 0 {
			return false
		}
		if fn&1 == 1 || fn == sn {
			fr = NodeHash(c, fr)
			sr = NodeHash(c, sr)
			if fn&1 == 0 {
				for fn&1 == 0 && fn != 0 {
					fn >>= 1
					sn >>= 1
				}
			}
		} else {
			sr = NodeHash(sr, c)
		}
		fn >>= 1
		sn >>= 1
	}
	return sn == 0 && bytes.Equal(fr[:], firstRoot[:]) && bytes.Equal(sr[:], secondRoot[:])
}
