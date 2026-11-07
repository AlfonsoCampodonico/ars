// Package protocol implements the Accountable Replicated Saga (ARS)
// protocol as specified in AccountableSaga.tla: signed log entries, saga
// definitions, deterministic plans, and Evaluate, a pure function from
// (definition, log, time) to the saga's state, evidence and settlement.
package protocol

import (
	"crypto/ed25519"
	"encoding/json"
	"errors"
	"fmt"
	"time"
)

// Kind is the type of a signed log entry. Names match the TLA+ spec.
type Kind string

const (
	KVote        Kind = "vote"        // plan result (hex hash) or Abort
	KEffect      Kind = "effect"      // owner: side effect performed
	KConfirm     Kind = "confirm"     // beneficiary: effect observed
	KDispute     Kind = "dispute"     // beneficiary: effect NOT observed
	KReceipt     Kind = "receipt"     // any org: local state for step undone
	KUndo        Kind = "undo"        // owner: side effect undone
	KUndoOk      Kind = "undoOk"      // beneficiary: undo observed
	KUndoDispute Kind = "undoDispute" // beneficiary: undo NOT observed
	KODone       Kind = "oDone"       // oracle: effect happened
	KOUndone     Kind = "oUndone"     // oracle: effect undone
)

// Abort is the vote value meaning "re-executing this plan fails".
const Abort = "ABORT"

// Entry is a statement signed by an org or oracle and stored on the log.
type Entry struct {
	Saga string `json:"saga"`
	Kind Kind   `json:"kind"`
	From string `json:"from"`
	Step int    `json:"step"`
	Val  string `json:"val,omitempty"` // vote value
	Ref  string `json:"ref,omitempty"` // external reference, e.g. a charge ID
	Note string `json:"note,omitempty"`
	Sig  []byte `json:"sig,omitempty"`
}

func (e Entry) signingBytes() []byte {
	e.Sig = nil
	b, _ := json.Marshal(e)
	return append([]byte("ars-entry-v1\n"), b...)
}

// Sign returns e signed with key.
func (e Entry) Sign(key ed25519.PrivateKey) Entry {
	e.Sig = ed25519.Sign(key, e.signingBytes())
	return e
}

// Verify checks e's signature.
func (e Entry) Verify(pub ed25519.PublicKey) bool {
	return len(pub) == ed25519.PublicKeySize && ed25519.Verify(pub, e.signingBytes(), e.Sig)
}

// Duration is a time.Duration that (un)marshals as a string like "10m".
type Duration struct{ time.Duration }

func (d Duration) MarshalJSON() ([]byte, error) { return json.Marshal(d.String()) }
func (d *Duration) UnmarshalJSON(b []byte) error {
	var s string
	if err := json.Unmarshal(b, &s); err != nil {
		return err
	}
	v, err := time.ParseDuration(s)
	d.Duration = v
	return err
}

// Party is an org or oracle with its signing key.
type Party struct {
	Name   string            `json:"name"`
	PubKey ed25519.PublicKey `json:"pubkey"`
}

// StepDef describes one saga step.
type StepDef struct {
	Name       string   `json:"name"`
	Deps       []int    `json:"deps"`             // indices of earlier steps
	Plan       string   `json:"plan"`             // deterministic plan, see Plans
	Owner      string   `json:"owner"`            // performs the side effect
	Benef      string   `json:"benef"`            // observes the side effect
	Oracle     string   `json:"oracle,omitempty"` // trusted oracle, if any
	PlanDur    Duration `json:"plan_window"`      // all orgs vote
	EffectDur  Duration `json:"effect_window"`    // owner attests the effect
	RespondDur Duration `json:"respond_window"`   // beneficiary confirms or disputes
}

// SagaDef is agreed by all orgs before the saga starts.
type SagaDef struct {
	ID             string          `json:"id"`
	Start          time.Time       `json:"start"`
	Orgs           []Party         `json:"orgs"`
	Oracles        []Party         `json:"oracles,omitempty"`
	Steps          []StepDef       `json:"steps"`
	CompDur        Duration        `json:"compensation_window"`         // receipts and undo attestations
	CompRespondDur Duration        `json:"compensation_respond_window"` // beneficiaries check undos
	Terms          json.RawMessage `json:"terms"`                       // input to every plan
	Bond           int64           `json:"bond_cents"`
}

// Validate checks structural rules the spec ASSUMEs.
func (d *SagaDef) Validate() error {
	orgs := map[string]bool{}
	for _, o := range d.Orgs {
		if len(o.PubKey) != ed25519.PublicKeySize {
			return fmt.Errorf("org %q: bad public key", o.Name)
		}
		orgs[o.Name] = true
	}
	oracles := map[string]bool{}
	for _, o := range d.Oracles {
		if orgs[o.Name] {
			return fmt.Errorf("%q is both an org and an oracle", o.Name)
		}
		oracles[o.Name] = true
	}
	if len(d.Steps) == 0 {
		return errors.New("saga has no steps")
	}
	for i, s := range d.Steps {
		for _, dep := range s.Deps {
			if dep < 0 || dep >= i {
				return fmt.Errorf("step %d: deps must refer to earlier steps", i)
			}
		}
		if !orgs[s.Owner] || !orgs[s.Benef] || s.Owner == s.Benef {
			return fmt.Errorf("step %d: owner and beneficiary must be distinct orgs", i)
		}
		if s.Oracle != "" && !oracles[s.Oracle] {
			return fmt.Errorf("step %d: unknown oracle %q", i, s.Oracle)
		}
		if s.PlanDur.Duration <= 0 || s.EffectDur.Duration <= 0 || s.RespondDur.Duration <= 0 {
			return fmt.Errorf("step %d: windows must be positive", i)
		}
	}
	if d.CompDur.Duration <= 0 || d.CompRespondDur.Duration <= 0 {
		return errors.New("compensation windows must be positive")
	}
	return nil
}

func (d *SagaDef) key(name string) ed25519.PublicKey {
	for _, p := range d.Orgs {
		if p.Name == name {
			return p.PubKey
		}
	}
	for _, p := range d.Oracles {
		if p.Name == name {
			return p.PubKey
		}
	}
	return nil
}

func (d *SagaDef) isOrg(name string) bool {
	for _, p := range d.Orgs {
		if p.Name == name {
			return true
		}
	}
	return false
}

// Record is an entry as stored on the log, with the log's timestamp.
type Record struct {
	Entry Entry
	Time  time.Time
	Index uint64
}
