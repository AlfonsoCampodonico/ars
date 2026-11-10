// Package oracle is a mock payment processor acting as a trusted oracle:
// whenever a capture or refund really happens, it posts a signed report to
// the saga log, the way a real PSP would send a signed webhook.
package oracle

import (
	"crypto/ed25519"
	"fmt"
	"sync"
	"time"

	"github.com/AlfonsoCampodonico/ars/protocol"
	"github.com/AlfonsoCampodonico/ars/translog"
)

// Charge is a captured payment.
type Charge struct {
	ID       string `json:"id"`
	Saga     string `json:"saga"`
	Step     int    `json:"step"`
	Amount   int64  `json:"amount_cents"`
	Refunded bool   `json:"refunded"`
}

// PSP is the mock payment processor.
type PSP struct {
	Name      string
	Key       ed25519.PrivateKey
	Log       translog.API
	LogOrigin string
	LogKey    ed25519.PublicKey
	Gossip    protocol.Gossip // reports the log refuses are gossiped as claims
	Clock     func() time.Time

	mu      sync.Mutex
	charges map[string]*Charge
	n       int
	subs    map[string]*protocol.Submitter // per saga
}

func (p *PSP) submitter(saga string) *protocol.Submitter {
	if p.subs == nil {
		p.subs = map[string]*protocol.Submitter{}
	}
	if p.subs[saga] == nil {
		p.subs[saga] = &protocol.Submitter{Saga: saga, From: p.Name, Key: p.Key, Log: p.Log,
			LogOrigin: p.LogOrigin, LogKey: p.LogKey, Gossip: p.Gossip, Clock: p.Clock}
	}
	return p.subs[saga]
}

func (p *PSP) report(saga string, step int, kind protocol.Kind, ref string) error {
	return p.submitter(saga).Submit(protocol.Entry{Kind: kind, Step: step, Ref: ref})
}

// Audit checks that the log still holds every report it gave a receipt for.
func (p *PSP) Audit() error {
	recs, err := protocol.ReadRecords(p.Log)
	if err != nil {
		return err
	}
	p.mu.Lock()
	subs := make([]*protocol.Submitter, 0, len(p.subs))
	for _, s := range p.subs {
		subs = append(subs, s)
	}
	p.mu.Unlock()
	for _, s := range subs {
		if err := s.Audit(recs); err != nil {
			return err
		}
	}
	return nil
}

// Capture moves money and reports it.
func (p *PSP) Capture(saga string, step int, amount int64) (string, error) {
	p.mu.Lock()
	defer p.mu.Unlock()
	if p.charges == nil {
		p.charges = map[string]*Charge{}
	}
	p.n++
	c := &Charge{ID: fmt.Sprintf("ch_%04d", p.n), Saga: saga, Step: step, Amount: amount}
	p.charges[c.ID] = c
	return c.ID, p.report(saga, step, protocol.KODone, c.ID)
}

// Refund reverses a capture and reports it.
func (p *PSP) Refund(id string) error {
	p.mu.Lock()
	defer p.mu.Unlock()
	c, ok := p.charges[id]
	if !ok || c.Refunded {
		return fmt.Errorf("psp: no refundable charge %q", id)
	}
	c.Refunded = true
	return p.report(c.Saga, c.Step, protocol.KOUndone, id)
}

// Lookup is what a buyer's agent sees on its card statement.
func (p *PSP) Lookup(saga string, step int) (Charge, bool) {
	p.mu.Lock()
	defer p.mu.Unlock()
	for _, c := range p.charges {
		if c.Saga == saga && c.Step == step {
			return *c, true
		}
	}
	return Charge{}, false
}
