// Package translog is a small append-only transparency log: timestamped
// entries in an RFC 9162 Merkle tree, with a signed checkpoint (tree head)
// for every tree size, inclusion and consistency proofs, and fork detection
// between views by comparing signed checkpoints.
package translog

import (
	"crypto/ed25519"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"sync"
	"time"

	"github.com/AlfonsoCampodonico/ars/merkle"
)

// Leaf is one stored entry. The log assigns Index and Time.
type Leaf struct {
	Index uint64    `json:"index"`
	Time  time.Time `json:"time"`
	Data  []byte    `json:"data"`
}

// Bytes is the exact byte string hashed into the tree: 8-byte big-endian
// unix nanoseconds followed by the entry data.
func (l Leaf) Bytes() []byte {
	b := make([]byte, 8, 8+len(l.Data))
	binary.BigEndian.PutUint64(b, uint64(l.Time.UnixNano()))
	return append(b, l.Data...)
}

// Checkpoint is a signed tree head.
type Checkpoint struct {
	Origin string    `json:"origin"`
	Size   uint64    `json:"size"`
	Root   string    `json:"root"` // hex
	Time   time.Time `json:"time"`
	Sig    []byte    `json:"sig"`
}

func (c Checkpoint) signed() []byte {
	return []byte(fmt.Sprintf("%s\n%d\n%s\n%d\n", c.Origin, c.Size, c.Root, c.Time.UnixNano()))
}

// Verify checks the operator's signature.
func (c Checkpoint) Verify(pub ed25519.PublicKey) bool {
	return ed25519.Verify(pub, c.signed(), c.Sig)
}

// API is what clients (sidecars, witnesses) need from a log.
type API interface {
	Append(data []byte) (Leaf, error)
	Entries(from uint64) ([]Leaf, error)
	Latest() (Checkpoint, error)
	CheckpointAt(size uint64) (Checkpoint, error)
	ConsistencyProof(from, to uint64) ([]merkle.Hash, error)
	InclusionProof(index, size uint64) ([]merkle.Hash, error)
}

// Log is an in-memory log. It is safe for concurrent use.
type Log struct {
	mu     sync.Mutex
	origin string
	key    ed25519.PrivateKey
	clock  func() time.Time
	leaves []Leaf
	hashes []merkle.Hash
	cps    []Checkpoint // cps[n] = checkpoint at size n
}

// New creates a log signed by key. clock defaults to time.Now.
func New(origin string, key ed25519.PrivateKey, clock func() time.Time) *Log {
	if clock == nil {
		clock = time.Now
	}
	l := &Log{origin: origin, key: key, clock: clock}
	l.cps = []Checkpoint{l.sign(0, merkle.EmptyRoot())}
	return l
}

// PublicKey returns the operator key that signs checkpoints.
func (l *Log) PublicKey() ed25519.PublicKey { return l.key.Public().(ed25519.PublicKey) }

func (l *Log) sign(size uint64, root merkle.Hash) Checkpoint {
	c := Checkpoint{Origin: l.origin, Size: size, Root: hex.EncodeToString(root[:]), Time: l.clock()}
	c.Sig = ed25519.Sign(l.key, c.signed())
	return c
}

// Append stores data with the log's current timestamp.
func (l *Log) Append(data []byte) (Leaf, error) {
	l.mu.Lock()
	defer l.mu.Unlock()
	lf := Leaf{Index: uint64(len(l.leaves)), Time: l.clock(), Data: append([]byte(nil), data...)}
	l.leaves = append(l.leaves, lf)
	l.hashes = append(l.hashes, merkle.LeafHash(lf.Bytes()))
	l.cps = append(l.cps, l.sign(uint64(len(l.hashes)), merkle.Root(l.hashes)))
	return lf, nil
}

func (l *Log) Entries(from uint64) ([]Leaf, error) {
	l.mu.Lock()
	defer l.mu.Unlock()
	if from > uint64(len(l.leaves)) {
		return nil, errors.New("translog: from beyond size")
	}
	return append([]Leaf(nil), l.leaves[from:]...), nil
}

func (l *Log) Latest() (Checkpoint, error) {
	l.mu.Lock()
	defer l.mu.Unlock()
	return l.cps[len(l.cps)-1], nil
}

func (l *Log) CheckpointAt(size uint64) (Checkpoint, error) {
	l.mu.Lock()
	defer l.mu.Unlock()
	if size >= uint64(len(l.cps)) {
		return Checkpoint{}, errors.New("translog: no checkpoint at that size")
	}
	return l.cps[size], nil
}

func (l *Log) ConsistencyProof(from, to uint64) ([]merkle.Hash, error) {
	l.mu.Lock()
	defer l.mu.Unlock()
	if to > uint64(len(l.hashes)) {
		return nil, errors.New("translog: size beyond log")
	}
	return merkle.ConsistencyProof(from, l.hashes[:to])
}

func (l *Log) InclusionProof(index, size uint64) ([]merkle.Hash, error) {
	l.mu.Lock()
	defer l.mu.Unlock()
	if size > uint64(len(l.hashes)) {
		return nil, errors.New("translog: size beyond log")
	}
	return merkle.InclusionProof(index, l.hashes[:size])
}

// Fork returns an independent copy that shares history so far and then
// diverges. It exists to simulate an equivocating operator in tests and
// demos: the operator signs both views with the same key.
func (l *Log) Fork() *Log {
	l.mu.Lock()
	defer l.mu.Unlock()
	return &Log{
		origin: l.origin, key: l.key, clock: l.clock,
		leaves: append([]Leaf(nil), l.leaves...),
		hashes: append([]merkle.Hash(nil), l.hashes...),
		cps:    append([]Checkpoint(nil), l.cps...),
	}
}

// ForkProof is two checkpoints of the same size, validly signed by the same
// operator, with different roots. Anyone holding the operator's public key
// can verify it; an honest operator can never produce one.
type ForkProof struct {
	A, B Checkpoint
}

// Valid reports whether the proof convicts the operator holding pub.
func (p ForkProof) Valid(pub ed25519.PublicKey) bool {
	return p.A.Origin == p.B.Origin && p.A.Size == p.B.Size && p.A.Root != p.B.Root &&
		p.A.Verify(pub) && p.B.Verify(pub)
}

// CompareViews is the gossip step between two orgs: each fetches the
// checkpoint from its own view at the smaller of the two sizes, and the
// signed checkpoints are compared. It returns a fork proof if the views
// disagree on any shared prefix. It also checks each view is internally
// consistent (its latest head extends the compared one).
func CompareViews(pub ed25519.PublicKey, mine, theirs API) (*ForkProof, error) {
	a, err := mine.Latest()
	if err != nil {
		return nil, err
	}
	b, err := theirs.Latest()
	if err != nil {
		return nil, err
	}
	if !a.Verify(pub) || !b.Verify(pub) {
		return nil, errors.New("translog: checkpoint with bad signature")
	}
	size := min(a.Size, b.Size)
	ca, err := mine.CheckpointAt(size)
	if err != nil {
		return nil, err
	}
	cb, err := theirs.CheckpointAt(size)
	if err != nil {
		return nil, err
	}
	if ca.Root != cb.Root {
		p := &ForkProof{A: ca, B: cb}
		if p.Valid(pub) {
			return p, nil
		}
		return nil, errors.New("translog: views differ but checkpoints are not validly signed")
	}
	for _, v := range []struct {
		api        API
		small, big Checkpoint
	}{{mine, ca, a}, {theirs, cb, b}} {
		if err := verifyExtends(v.api, v.small, v.big); err != nil {
			return nil, err
		}
	}
	return nil, nil
}

func verifyExtends(api API, small, big Checkpoint) error {
	if small.Size == 0 || small.Size == big.Size {
		return nil
	}
	proof, err := api.ConsistencyProof(small.Size, big.Size)
	if err != nil {
		return err
	}
	r1, err := decodeRoot(small.Root)
	if err != nil {
		return err
	}
	r2, err := decodeRoot(big.Root)
	if err != nil {
		return err
	}
	if !merkle.VerifyConsistency(small.Size, big.Size, r1, r2, proof) {
		return errors.New("translog: view is not append-only")
	}
	return nil
}

func decodeRoot(s string) (merkle.Hash, error) {
	var h merkle.Hash
	b, err := hex.DecodeString(s)
	if err != nil || len(b) != len(h) {
		return h, errors.New("translog: bad root encoding")
	}
	copy(h[:], b)
	return h, nil
}
