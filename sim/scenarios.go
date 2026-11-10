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
			Bonds: returned(),
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
			Bonds: with(returned(), Merchant, protocol.BondSlashed), Accused: []string{Merchant},
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
			Bonds: with(returned(), Merchant, protocol.BondSlashed), Accused: []string{Merchant},
		},
		{
			Name: "carrier-lies",
			Story: "The carrier claims it delivered, but the parcel never arrives. The buyer disputes. " +
				"No oracle covers delivery, so the protocol can only narrow it to carrier vs buyer.",
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
			Bonds: with(returned(), Carrier, protocol.BondFrozen, Buyer, protocol.BondFrozen),
		},
		{
			Name: "undeliverable",
			Story: "The term sheet has no shipping address, so the 'ship' plan deterministically fails. " +
				"Everyone votes ABORT -- a justified veto. The saga unwinds and nobody is blamed.",
			Terms: noAddress, Setup: func(*World) {},
			Bonds: returned(),
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
			Bonds: with(returned(), Merchant, protocol.BondSlashed), Accused: []string{Merchant},
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
			Bonds: with(returned(), Carrier, protocol.BondSlashed), Accused: []string{Carrier},
		},
	}
}

// Build creates the world for a scenario.
func (s Scenario) Build() *World {
	w := NewWorld(s.Terms())
	s.Setup(w)
	return w
}
