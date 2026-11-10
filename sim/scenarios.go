package sim

import (
	"encoding/json"

	"github.com/AlfonsoCampodonico/ars/protocol"
	"github.com/AlfonsoCampodonico/ars/sidecar"
)

// Scenario is a named checkout run with its expected outcome.
type Scenario struct {
	Name, Story string
	Terms       func() protocol.CheckoutTerms
	Setup       func(w *World)
	// Expected bonds at settlement and orgs expected to be accused.
	Bonds   map[string]string
	Accused []string
	// Card is what the buyer's card statement shows at the end.
	Card string
	// Censored lists who claims the log operator refused an entry, and
	// OperatorBlamed whether a broken receipt proves it.
	Censored       []string
	OperatorBlamed bool
}

func returned() map[string]string {
	return map[string]string{Buyer: protocol.BondReturned, Merchant: protocol.BondReturned, Carrier: protocol.BondReturned}
}

func with(m map[string]string, kv ...string) map[string]string {
	for i := 0; i+1 < len(kv); i += 2 {
		m[kv[i]] = kv[i+1]
	}
	return m
}

// Scenarios is the catalogue used by the demo and the tests.
func Scenarios() []Scenario {
	noAddress := func() protocol.CheckoutTerms { t := CheckoutTerms(); t.ShipTo = ""; return t }
	return []Scenario{
		{
			Name:  "happy",
			Story: "Everyone behaves. Terms lock, payment and reservation run in parallel, the carrier delivers.",
			Terms: CheckoutTerms, Setup: func(*World) {},
			Bonds: returned(), Card: "done",
		},
		{
			Name: "tampered-merchant",
			Story: "The merchant's software was modified to add a hidden €18 fee to the total. " +
				"Its vote on 'lock terms' doesn't match what everyone else re-executes.",
			Terms: CheckoutTerms,
			Setup: func(w *World) {
				m := w.Org(Merchant).Car
				p := protocol.CheckoutPlans()
				honest := p["checkout.lock"]
				p["checkout.lock"] = func(raw json.RawMessage, s int) ([]byte, error) {
					var t protocol.CheckoutTerms
					_ = json.Unmarshal(raw, &t)
					t.ShippingCents += 1800 // the hidden fee
					b, _ := json.Marshal(t)
					return honest(b, s)
				}
				m.Plans = p
			},
			Bonds: with(returned(), Merchant, protocol.BondSlashed), Accused: []string{Merchant}, Card: "no",
		},
		{
			Name: "fake-capture",
			Story: "The merchant's agent claims it captured the payment, but never charged the card. " +
				"The payment processor (oracle) never reports a capture.",
			Terms: CheckoutTerms,
			Setup: func(w *World) {
				w.Org(Merchant).Agent.Act = func(w *World, o *Org, t sidecar.Todo) bool {
					if t.Step == StepPay && t.Action == "attest_effect" {
						_ = o.Car.AttestEffect(t.Step, "ch_FAKE")
						w.logf("merchant claims payment captured (ch_FAKE) without charging")
						return true
					}
					return false
				}
			},
			Bonds: with(returned(), Merchant, protocol.BondSlashed), Accused: []string{Merchant}, Card: "no",
		},
		{
			Name: "carrier-lies",
			Story: "The carrier claims it delivered, but the parcel never arrives. The buyer disputes. " +
				"No oracle covers delivery, so the protocol can only narrow it to carrier vs buyer. " +
				"The saga holds: nothing is refunded automatically, both bonds wait for outside resolution.",
			Terms: CheckoutTerms,
			Setup: func(w *World) {
				w.Org(Carrier).Agent.Act = func(w *World, o *Org, t sidecar.Todo) bool {
					if t.Step == StepShip && t.Action == "attest_effect" {
						_ = o.Car.AttestEffect(t.Step, "trk-NEVER-SHIPPED")
						w.logf("carrier claims delivery without delivering")
						return true
					}
					return false
				}
			},
			Bonds: with(returned(), Carrier, protocol.BondFrozen, Buyer, protocol.BondFrozen), Card: "done",
		},
		{
			Name: "buyer-lies",
			Story: "The parcel arrives, but the buyer disputes the delivery to get a refund and keep it. " +
				"From the log this looks exactly like carrier-lies, so it ends the same way: the saga holds, " +
				"no refund is paid, and both bonds wait for outside resolution. Lying gains nothing.",
			Terms: CheckoutTerms,
			Setup: func(w *World) {
				w.Org(Buyer).Agent.Act = func(w *World, o *Org, t sidecar.Todo) bool {
					if t.Step == StepShip && t.Action == "observe_effect" {
						_ = o.Car.ObserveEffect(t.Step, false, "")
						w.logf("buyer received the parcel but disputes the delivery")
						return true
					}
					return false
				}
			},
			Bonds: with(returned(), Carrier, protocol.BondFrozen, Buyer, protocol.BondFrozen), Card: "done",
		},
		{
			Name: "buyer-ghosts",
			Story: "The parcel arrives and the buyer never answers. Ship aborts and payment is refunded, " +
				"but delivery can't be undone: it's the pivot, so the carrier owes no undo. " +
				"The silent buyer is slashed; its bond is what pays for the parcel.",
			Terms: CheckoutTerms,
			Setup: func(w *World) {
				w.Org(Buyer).Agent.Act = func(w *World, o *Org, t sidecar.Todo) bool {
					return t.Step == StepShip && t.Action == "observe_effect"
				}
			},
			Bonds: with(returned(), Buyer, protocol.BondSlashed), Accused: []string{Buyer}, Card: "undone",
		},
		{
			Name: "undeliverable",
			Story: "The term sheet has no shipping address, so the 'ship' plan deterministically fails. " +
				"Everyone votes ABORT -- a justified veto. The saga unwinds and nobody is blamed.",
			Terms: noAddress, Setup: func(*World) {},
			Bonds: returned(), Card: "undone",
		},
		{
			Name: "refund-dodger",
			Story: "Same as 'undeliverable', but during compensation the merchant claims it refunded " +
				"the buyer without doing it. The payment processor never reports a refund.",
			Terms: noAddress,
			Setup: func(w *World) {
				w.Org(Merchant).Agent.Act = func(w *World, o *Org, t sidecar.Todo) bool {
					if t.Step == StepPay && t.Action == "attest_undo" {
						_ = o.Car.AttestUndo(t.Step, "re_FAKE")
						w.logf("merchant claims refund (re_FAKE) without refunding")
						return true
					}
					return false
				}
			},
			Bonds: with(returned(), Merchant, protocol.BondSlashed), Accused: []string{Merchant}, Card: "done",
		},
		{
			Name: "carrier-vanishes",
			Story: "The carrier's systems go dark once payment and reservation are done. " +
				"Deadlines pass without its vote; the saga aborts instead of hanging, and the carrier is blamed.",
			Terms: CheckoutTerms,
			Setup: func(w *World) {
				w.Org(Carrier).Agent.Offline = func(w *World) bool {
					st := w.State()
					return st.Steps[StepPay].Stage == protocol.Committed
				}
			},
			Bonds: with(returned(), Carrier, protocol.BondSlashed), Accused: []string{Carrier}, Card: "undone",
		},
		{
			Name: "censored-vote",
			Story: "The log operator refuses the buyer's vote on 'lock terms'. The buyer gossips a signed claim " +
				"instead. Its vote never reaches the log, so the step aborts, but the buyer isn't blamed: " +
				"it's in an unresolved dispute with the operator, its bond frozen rather than slashed.",
			Terms: CheckoutTerms,
			Setup: func(w *World) {
				w.CensorLog(func(e protocol.Entry) string {
					if e.From == Buyer && e.Step == StepLock && e.Kind == protocol.KVote {
						return "refuse"
					}
					return ""
				})
			},
			Bonds: with(returned(), Buyer, protocol.BondFrozen), Card: "no", Censored: []string{Buyer},
		},
		{
			Name: "broken-promise",
			Story: "The log operator signs a receipt for the buyer's vote, then never stores it. The buyer's " +
				"sidecar notices the log doesn't hold what was promised and gossips the receipt. The step " +
				"aborts, and the receipt proves the operator alone misbehaved: every bond is returned.",
			Terms: CheckoutTerms,
			Setup: func(w *World) {
				w.CensorLog(func(e protocol.Entry) string {
					if e.From == Buyer && e.Step == StepLock && e.Kind == protocol.KVote {
						return "drop"
					}
					return ""
				})
			},
			Bonds: returned(), Card: "no", OperatorBlamed: true,
		},
	}
}

// Build creates the world for a scenario.
func (s Scenario) Build() *World {
	w := NewWorld(s.Terms())
	s.Setup(w)
	return w
}
