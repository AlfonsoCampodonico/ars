// Package sim runs checkout sagas end to end in-process: a fake clock, a
// transparency log, one sidecar per org, a mock PSP oracle, and scripted
// agents (honest or Byzantine) acting on a simulated real world.
package sim

import (
	"crypto/ed25519"
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"sync"
	"time"

	"ars/oracle"
	"ars/protocol"
	"ars/sidecar"
	"ars/translog"
)

// Clock is a manually advanced clock.
type Clock struct {
	mu sync.Mutex
	t  time.Time
}

func (c *Clock) Now() time.Time { c.mu.Lock(); defer c.mu.Unlock(); return c.t }
func (c *Clock) Advance(d time.Duration) {
	c.mu.Lock()
	c.t = c.t.Add(d)
	c.mu.Unlock()
}

// Key derives a deterministic demo key for a party name.
func Key(name string) ed25519.PrivateKey {
	seed := sha256.Sum256([]byte("ars-demo-key:" + name))
	return ed25519.NewKeyFromSeed(seed[:])
}

// Step indices of the checkout saga.
const (
	StepLock = iota
	StepPay
	StepReserve
	StepShip
)

// Org names.
const (
	Buyer    = "buyer"
	Merchant = "merchant"
	Carrier  = "carrier"
	PSPName  = "psp"
)

// CheckoutTerms is the demo term sheet.
func CheckoutTerms() protocol.CheckoutTerms {
	return protocol.CheckoutTerms{
		OrderID:  "ord-7731",
		Currency: "EUR",
		Items: []protocol.Item{
			{SKU: "espresso-machine", Qty: 1, UnitCents: 34900},
			{SKU: "descaler", Qty: 2, UnitCents: 1250},
		},
		TaxBPS:        2100,
		ShippingCents: 499,
		MaxTotalCents: 50000,
		ShipTo:        "Calle de Alcalá 1, Madrid",
		PickupSlot:    "2026-11-09T10:00/12:00",
	}
}

// CheckoutDef builds the 4-step checkout saga (see MCCheckout.tla).
// Windows are compressed for simulation; see README for production values.
func CheckoutDef(start time.Time, terms protocol.CheckoutTerms) *protocol.SagaDef {
	pub := func(n string) protocol.Party {
		return protocol.Party{Name: n, PubKey: Key(n).Public().(ed25519.PublicKey)}
	}
	d := func(s string) protocol.Duration { v, _ := time.ParseDuration(s); return protocol.Duration{Duration: v} }
	raw, _ := json.Marshal(terms)
	return &protocol.SagaDef{
		ID:      "saga-" + terms.OrderID,
		Start:   start,
		Orgs:    []protocol.Party{pub(Buyer), pub(Merchant), pub(Carrier)},
		Oracles: []protocol.Party{pub(PSPName)},
		Steps: []protocol.StepDef{
			{Name: "lock terms", Plan: "checkout.lock", Owner: Merchant, Benef: Buyer, PlanDur: d("3m"), EffectDur: d("5m"), RespondDur: d("5m")},
			{Name: "pay", Deps: []int{StepLock}, Plan: "checkout.pay", Owner: Merchant, Benef: Buyer, Oracle: PSPName, PlanDur: d("3m"), EffectDur: d("10m"), RespondDur: d("5m")},
			{Name: "reserve", Deps: []int{StepLock}, Plan: "checkout.reserve", Owner: Merchant, Benef: Carrier, PlanDur: d("3m"), EffectDur: d("10m"), RespondDur: d("5m")},
			{Name: "ship", Deps: []int{StepPay, StepReserve}, Plan: "checkout.ship", Owner: Carrier, Benef: Buyer, PlanDur: d("3m"), EffectDur: d("30m"), RespondDur: d("10m")},
		},
		CompDur:        d("20m"),
		CompRespondDur: d("10m"),
		Terms:          raw,
		Bond:           10000,
	}
}

// Agent decides what an org does in the real world each tick. Act returns
// true if it handled the todo; otherwise the honest default runs.
type Agent struct {
	Act     func(w *World, o *Org, t sidecar.Todo) bool
	Offline func(w *World) bool    // sidecar and agent unreachable
	Raw     func(w *World, o *Org) // free-form Byzantine behaviour each tick
}

// Org is one participant.
type Org struct {
	Name  string
	Car   *sidecar.Sidecar
	Agent Agent
}

// World is one simulated saga.
type World struct {
	Clock *Clock
	Log   *translog.Log
	Def   *protocol.SagaDef
	PSP   *oracle.PSP
	Orgs  []*Org
	Real  []string // per step: "no", "done", "undone" -- what really happened
	Refs  []string
	Trace []string
}

// NewWorld wires up a checkout saga with honest defaults.
func NewWorld(terms protocol.CheckoutTerms) *World {
	clock := &Clock{t: time.Date(2026, 11, 8, 9, 0, 0, 0, time.UTC)}
	log := translog.New("ars-demo-log", Key("log-operator"), clock.Now)
	def := CheckoutDef(clock.Now().Add(time.Minute), terms)
	w := &World{
		Clock: clock, Log: log, Def: def,
		PSP:  &oracle.PSP{Name: PSPName, Key: Key(PSPName), Log: log},
		Real: make([]string, len(def.Steps)), Refs: make([]string, len(def.Steps)),
	}
	for i := range w.Real {
		w.Real[i] = "no"
	}
	for _, n := range []string{Buyer, Merchant, Carrier} {
		w.Orgs = append(w.Orgs, &Org{Name: n, Car: &sidecar.Sidecar{
			Org: n, Key: Key(n), Def: def, Plans: protocol.CheckoutPlans(), Log: log, Clock: clock.Now,
		}})
	}
	return w
}

// Org returns a participant by name.
func (w *World) Org(name string) *Org {
	for _, o := range w.Orgs {
		if o.Name == name {
			return o
		}
	}
	return nil
}

func (w *World) logf(format string, a ...any) {
	w.Trace = append(w.Trace, fmt.Sprintf("%s  %s", w.Clock.Now().Format("15:04"), fmt.Sprintf(format, a...)))
}

func (w *World) amount() int64 {
	var t protocol.CheckoutTerms
	_ = json.Unmarshal(w.Def.Terms, &t)
	tot, _ := protocol.ComputeTotals(t)
	return tot.Total
}

// DoEffect really performs step's side effect (as its owner would).
func (w *World) DoEffect(step int) string {
	if w.Def.Steps[step].Oracle != "" {
		id, err := w.PSP.Capture(w.Def.ID, step, w.amount())
		if err != nil {
			w.logf("psp capture failed: %v", err)
		}
		w.Refs[step] = id
	} else {
		w.Refs[step] = fmt.Sprintf("ref-%s-%d", w.Def.Steps[step].Name, step)
	}
	w.Real[step] = "done"
	return w.Refs[step]
}

// UndoEffect really undoes step's side effect.
func (w *World) UndoEffect(step int) string {
	if w.Def.Steps[step].Oracle != "" && w.Real[step] == "done" {
		if err := w.PSP.Refund(w.Refs[step]); err != nil {
			w.logf("psp refund failed: %v", err)
		}
	}
	if w.Real[step] == "done" {
		w.Real[step] = "undone"
	}
	return "undo-" + w.Refs[step]
}

// Observed is what a beneficiary can check independently.
func (w *World) Observed(step int) string {
	if w.Def.Steps[step].Oracle != "" {
		if c, ok := w.PSP.Lookup(w.Def.ID, step); ok {
			if c.Refunded {
				return "undone"
			}
			return "done"
		}
		return "no"
	}
	return w.Real[step]
}

// Honest is what a well-behaved agent does with a todo.
func Honest(w *World, o *Org, t sidecar.Todo) {
	var err error
	switch t.Action {
	case "attest_effect":
		ref := w.DoEffect(t.Step)
		err = o.Car.AttestEffect(t.Step, ref)
		w.logf("%s performs %q (%s) and attests", o.Name, t.Name, ref)
	case "observe_effect":
		ok := w.Observed(t.Step) == "done"
		err = o.Car.ObserveEffect(t.Step, ok, "")
		w.logf("%s checks %q: happened=%v", o.Name, t.Name, ok)
	case "attest_undo":
		ref := w.UndoEffect(t.Step)
		err = o.Car.AttestUndo(t.Step, ref)
		w.logf("%s undoes %q and attests", o.Name, t.Name)
	case "observe_undo":
		ok := w.Observed(t.Step) != "done"
		err = o.Car.ObserveUndo(t.Step, ok, "")
		w.logf("%s checks undo of %q: undone=%v", o.Name, t.Name, ok)
	}
	if err != nil {
		w.logf("%s: %v", o.Name, err)
	}
}

// Post signs and appends an arbitrary entry as org (Byzantine behaviour).
func (w *World) Post(org string, e protocol.Entry) {
	e.Saga, e.From = w.Def.ID, org
	b, _ := json.Marshal(e.Sign(Key(org)))
	_, _ = w.Log.Append(b)
}

// State evaluates the saga now.
func (w *World) State() *protocol.State {
	st, err := w.Org(Buyer).Car.State()
	if err != nil {
		panic(err)
	}
	return st
}

// Run ticks every org once per simulated minute until the saga finishes.
func (w *World) Run(limit time.Duration) *protocol.State {
	end := w.Clock.Now().Add(limit)
	stages := ""
	for w.Clock.Now().Before(end) {
		for _, o := range w.Orgs {
			if o.Agent.Offline != nil && o.Agent.Offline(w) {
				continue
			}
			if o.Agent.Raw != nil {
				o.Agent.Raw(w, o)
				continue
			}
			todos, err := o.Car.Tick()
			if err != nil {
				w.logf("%s sidecar: %v", o.Name, err)
				continue
			}
			for _, t := range todos {
				if o.Agent.Act == nil || !o.Agent.Act(w, o, t) {
					Honest(w, o, t)
				}
			}
		}
		st := w.State()
		if s := fmt.Sprint(stageList(st)); s != stages {
			stages = s
			w.logf("log says: %s  compensation=%s", s, st.Comp)
		}
		if st.Finished {
			return st
		}
		w.Clock.Advance(time.Minute)
	}
	return w.State()
}

func stageList(st *protocol.State) []string {
	out := make([]string, len(st.Steps))
	for i, s := range st.Steps {
		out[i] = fmt.Sprintf("%s:%s", s.Name, s.Stage)
	}
	return out
}
