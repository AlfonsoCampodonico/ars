// Package sidecar is the per-org protocol runtime. It holds the org's
// signing key, re-executes plans and votes on its own, posts receipts, and
// exposes a narrow set of actions to the org's agent. The agent (an LLM)
// never signs anything directly and can never choose a vote value: it can
// only report facts about side effects it performed or observed.
package sidecar

import (
	"crypto/ed25519"
	"errors"
	"fmt"
	"slices"
	"sync"
	"time"

	"github.com/AlfonsoCampodonico/ars/protocol"
	"github.com/AlfonsoCampodonico/ars/translog"
)

// Sidecar runs the protocol for one org in one saga.
type Sidecar struct {
	Org   string
	Key   ed25519.PrivateKey
	Def   *protocol.SagaDef
	Plans protocol.Plans
	Log   translog.API
	// Gossip carries censorship claims between the saga's parties.
	Gossip protocol.Gossip
	Clock  func() time.Time
	// LocalUndo is called before posting a receipt for a committed step,
	// to roll back the org's own bookkeeping. Optional.
	LocalUndo func(step int) error

	mu   sync.Mutex
	subm *protocol.Submitter
}

func (s *Sidecar) submitter() *protocol.Submitter {
	if s.subm == nil {
		s.subm = &protocol.Submitter{Saga: s.Def.ID, From: s.Org, Key: s.Key, Log: s.Log,
			LogOrigin: s.Def.LogOrigin, LogKey: s.Def.LogKey, Gossip: s.Gossip, Clock: s.Clock}
	}
	return s.subm
}

// Todo is something the agent has to do in the real world, after which it
// reports back through one of the action methods.
type Todo struct {
	Step   int    `json:"step"`
	Name   string `json:"name"`
	Action string `json:"action"` // attest_effect, observe_effect, attest_undo, observe_undo
	Hint   string `json:"hint"`
	Due    string `json:"due"`
}

func (s *Sidecar) now() time.Time {
	if s.Clock != nil {
		return s.Clock()
	}
	return time.Now()
}

// State evaluates the saga from the log and the gossiped claims.
func (s *Sidecar) State() (*protocol.State, error) {
	recs, err := protocol.ReadRecords(s.Log)
	if err != nil {
		return nil, err
	}
	claims, err := s.Gossip.Claims()
	if err != nil {
		return nil, err
	}
	return protocol.Evaluate(s.Def, s.Plans, recs, claims, s.now())
}

// posted reports whether this org ever signed an entry of one of these kinds
// for step, on the log or in a claim -- so an honest sidecar never
// contradicts itself.
func (s *Sidecar) posted(step int, kinds ...protocol.Kind) (bool, error) {
	if s.submitter().Claimed(step, kinds...) {
		return true, nil
	}
	recs, err := protocol.ReadRecords(s.Log)
	if err != nil {
		return false, err
	}
	for _, r := range recs {
		e := r.Entry
		if e.Saga == s.Def.ID && e.From == s.Org && e.Step == step && slices.Contains(kinds, e.Kind) {
			return true, nil
		}
	}
	return false, nil
}

func (s *Sidecar) post(e protocol.Entry) error { return s.submitter().Submit(e) }

// Tick does everything the org does automatically: vote on open plans and,
// during compensation, undo local state and post receipts in reverse
// topological order. It returns the agent's outstanding real-world tasks.
func (s *Sidecar) Tick() ([]Todo, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	recs, err := protocol.ReadRecords(s.Log)
	if err != nil {
		return nil, err
	}
	if err := s.submitter().Audit(recs); err != nil { // the log must hold what it signed for
		return nil, err
	}
	st, err := s.State()
	if err != nil {
		return nil, err
	}
	for i, step := range st.Steps {
		if step.Stage != protocol.PlanPh {
			continue
		}
		if done, err := s.posted(i, protocol.KVote); err != nil || done {
			if err != nil {
				return nil, err
			}
			continue
		}
		v, err := s.Plans.Run(s.Def.Steps[i].Plan, s.Def.Terms, i)
		if err != nil {
			return nil, err
		}
		if err := s.post(protocol.Entry{Kind: protocol.KVote, Step: i, Val: v}); err != nil {
			return nil, err
		}
	}
	if st.Comp == "open" { // receipts are due within the undo window
		if err := s.receipts(st); err != nil {
			return nil, err
		}
	}
	if st, err = s.State(); err != nil {
		return nil, err
	}
	return s.todos(st), nil
}

func (s *Sidecar) receipts(st *protocol.State) error {
	for progress := true; progress; {
		progress = false
		for t := len(st.Steps) - 1; t >= 0; t-- {
			if !st.OwesReceipt(t) || st.Filed(protocol.KReceipt, s.Org, t) {
				continue
			}
			if done, err := s.posted(t, protocol.KReceipt); err != nil || done {
				if err != nil {
					return err
				}
				continue
			}
			blocked := false // a committed dependent not yet undone
			for u, sd := range s.Def.Steps {
				if slices.Contains(sd.Deps, t) && st.OwesReceipt(u) {
					if ok, err := s.posted(u, protocol.KReceipt); err != nil || !ok {
						if err != nil {
							return err
						}
						blocked = true
					}
				}
			}
			if blocked {
				continue
			}
			if s.LocalUndo != nil {
				if err := s.LocalUndo(t); err != nil {
					return fmt.Errorf("local undo of step %d: %w", t, err)
				}
			}
			if err := s.post(protocol.Entry{Kind: protocol.KReceipt, Step: t}); err != nil {
				return err
			}
			progress = true
		}
	}
	return nil
}

func (s *Sidecar) todos(st *protocol.State) []Todo {
	var out []Todo
	for i, sd := range s.Def.Steps {
		ss := st.Steps[i]
		due := ss.EffectDeadline.Format(time.RFC3339)
		if ss.Stage == protocol.EffectPh && sd.Owner == s.Org && !st.Filed(protocol.KEffect, s.Org, i) {
			out = append(out, Todo{i, sd.Name, "attest_effect",
				"perform this step's side effect, then report it with a reference (e.g. charge or tracking ID)", due})
		}
		if (ss.Stage == protocol.EffectPh || ss.Stage == protocol.RespondPh) && sd.Benef == s.Org && st.BenefDue(i) &&
			!st.Filed(protocol.KConfirm, s.Org, i) && !st.Filed(protocol.KDispute, s.Org, i) {
			out = append(out, Todo{i, sd.Name, "observe_effect",
				"check independently whether the owner's claimed effect really happened", due})
		}
		if st.Comp == "open" && sd.Owner == s.Org && st.OwesUndo(i) && !st.Filed(protocol.KUndo, s.Org, i) {
			out = append(out, Todo{i, sd.Name, "attest_undo",
				"undo this step's side effect (refund, cancel, return), then report it",
				st.UndoDeadline.Format(time.RFC3339)})
		}
		if (st.Comp == "open" || st.Comp == "respond") && sd.Benef == s.Org && st.UndoBenefDue(i) &&
			!st.Filed(protocol.KUndoOk, s.Org, i) && !st.Filed(protocol.KUndoDispute, s.Org, i) {
			out = append(out, Todo{i, sd.Name, "observe_undo",
				"check independently whether the owner really undid the effect", st.CompDeadline.Format(time.RFC3339)})
		}
	}
	return out
}

// ErrNotAllowed means the request would make this org violate the protocol.
var ErrNotAllowed = errors.New("not allowed")

func (s *Sidecar) check(step int) (*protocol.State, protocol.StepDef, error) {
	if step < 0 || step >= len(s.Def.Steps) {
		return nil, protocol.StepDef{}, fmt.Errorf("%w: no step %d", ErrNotAllowed, step)
	}
	st, err := s.State()
	return st, s.Def.Steps[step], err
}

// AttestEffect: the owner's agent reports it performed the side effect.
func (s *Sidecar) AttestEffect(step int, ref string) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	st, sd, err := s.check(step)
	if err != nil {
		return err
	}
	if sd.Owner != s.Org || st.Steps[step].Stage != protocol.EffectPh {
		return fmt.Errorf("%w: not the owner of an open effect phase", ErrNotAllowed)
	}
	if done, err := s.posted(step, protocol.KEffect); err != nil || done {
		return errors.Join(err, fmt.Errorf("%w: already attested", ErrNotAllowed))
	}
	return s.post(protocol.Entry{Kind: protocol.KEffect, Step: step, Ref: ref})
}

// ObserveEffect: the beneficiary's agent reports what it saw. Steps with an
// oracle are settled by the oracle, so there is nothing to observe there.
func (s *Sidecar) ObserveEffect(step int, happened bool, note string) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	st, sd, err := s.check(step)
	if err != nil {
		return err
	}
	ph := st.Steps[step].Stage
	if sd.Benef != s.Org || (ph != protocol.EffectPh && ph != protocol.RespondPh) || !st.BenefDue(step) {
		return fmt.Errorf("%w: nothing to observe on step %d", ErrNotAllowed, step)
	}
	if done, err := s.posted(step, protocol.KConfirm, protocol.KDispute); err != nil || done {
		return errors.Join(err, fmt.Errorf("%w: already responded", ErrNotAllowed))
	}
	kind := protocol.KDispute
	if happened {
		kind = protocol.KConfirm
	}
	return s.post(protocol.Entry{Kind: kind, Step: step, Note: note})
}

// AttestUndo: the owner's agent reports it undid the side effect.
func (s *Sidecar) AttestUndo(step int, ref string) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	st, sd, err := s.check(step)
	if err != nil {
		return err
	}
	if sd.Owner != s.Org || st.Comp != "open" || !st.OwesUndo(step) {
		return fmt.Errorf("%w: no undo owed on step %d", ErrNotAllowed, step)
	}
	if done, err := s.posted(step, protocol.KUndo); err != nil || done {
		return errors.Join(err, fmt.Errorf("%w: already attested", ErrNotAllowed))
	}
	return s.post(protocol.Entry{Kind: protocol.KUndo, Step: step, Ref: ref})
}

// ObserveUndo: the beneficiary's agent reports whether the undo happened.
func (s *Sidecar) ObserveUndo(step int, happened bool, note string) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	st, sd, err := s.check(step)
	if err != nil {
		return err
	}
	if sd.Benef != s.Org || (st.Comp != "open" && st.Comp != "respond") || !st.UndoBenefDue(step) {
		return fmt.Errorf("%w: no undo to observe on step %d", ErrNotAllowed, step)
	}
	if done, err := s.posted(step, protocol.KUndoOk, protocol.KUndoDispute); err != nil || done {
		return errors.Join(err, fmt.Errorf("%w: already responded", ErrNotAllowed))
	}
	kind := protocol.KUndoDispute
	if happened {
		kind = protocol.KUndoOk
	}
	return s.post(protocol.Entry{Kind: kind, Step: step, Note: note})
}
