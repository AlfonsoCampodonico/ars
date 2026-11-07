package protocol

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
)

// ErrPlanFails means the plan deterministically fails: every honest org
// votes Abort, and Abort is then a justified veto.
var ErrPlanFails = errors.New("plan fails")

// PlanFunc deterministically computes step's result from the agreed terms.
// It must not read clocks, randomness, the network or any local state.
type PlanFunc func(terms json.RawMessage, step int) ([]byte, error)

// Plans maps plan names to implementations. Every org runs the same code.
type Plans map[string]PlanFunc

// Run returns the vote value for a step: hex(sha256(result)) or Abort.
// Any other error (e.g. unknown plan) is returned as-is.
func (p Plans) Run(name string, terms json.RawMessage, step int) (string, error) {
	f, ok := p[name]
	if !ok {
		return "", fmt.Errorf("unknown plan %q", name)
	}
	out, err := f(terms, step)
	if errors.Is(err, ErrPlanFails) {
		return Abort, nil
	}
	if err != nil {
		return "", err
	}
	h := sha256.Sum256(out)
	return hex.EncodeToString(h[:]), nil
}

// CheckoutTerms is the term sheet both shopping agents sign off on.
type CheckoutTerms struct {
	OrderID       string `json:"order_id"`
	Currency      string `json:"currency"`
	Items         []Item `json:"items"`
	TaxBPS        int64  `json:"tax_bps"` // basis points
	ShippingCents int64  `json:"shipping_cents"`
	MaxTotalCents int64  `json:"max_total_cents"` // buyer's spend limit
	ShipTo        string `json:"ship_to"`
	PickupSlot    string `json:"pickup_slot"`
}

// Item is one order line.
type Item struct {
	SKU       string `json:"sku"`
	Qty       int64  `json:"qty"`
	UnitCents int64  `json:"unit_cents"`
}

// Totals are the money figures every org must agree on.
type Totals struct {
	Subtotal, Tax, Shipping, Total int64
}

// ComputeTotals is the canonical pricing function.
func ComputeTotals(t CheckoutTerms) (Totals, error) {
	var tot Totals
	if len(t.Items) == 0 {
		return tot, fmt.Errorf("%w: empty order", ErrPlanFails)
	}
	for _, it := range t.Items {
		if it.Qty <= 0 || it.UnitCents < 0 {
			return tot, fmt.Errorf("%w: bad line %s", ErrPlanFails, it.SKU)
		}
		tot.Subtotal += it.Qty * it.UnitCents
	}
	tot.Tax = tot.Subtotal * t.TaxBPS / 10_000 // truncating, by definition
	tot.Shipping = t.ShippingCents
	tot.Total = tot.Subtotal + tot.Tax + tot.Shipping
	if t.MaxTotalCents > 0 && tot.Total > t.MaxTotalCents {
		return tot, fmt.Errorf("%w: total %d exceeds buyer limit %d", ErrPlanFails, tot.Total, t.MaxTotalCents)
	}
	return tot, nil
}

func decodeTerms(raw json.RawMessage) (CheckoutTerms, error) {
	var t CheckoutTerms
	if err := json.Unmarshal(raw, &t); err != nil {
		return t, fmt.Errorf("%w: unreadable terms", ErrPlanFails)
	}
	return t, nil
}

// CheckoutPlans are the four checkout steps' plans.
func CheckoutPlans() Plans {
	return Plans{
		"checkout.lock": func(raw json.RawMessage, _ int) ([]byte, error) {
			t, err := decodeTerms(raw)
			if err != nil {
				return nil, err
			}
			tot, err := ComputeTotals(t)
			if err != nil {
				return nil, err
			}
			return json.Marshal(struct {
				OrderID string
				Items   []Item
				Totals  Totals
			}{t.OrderID, t.Items, tot})
		},
		"checkout.pay": func(raw json.RawMessage, _ int) ([]byte, error) {
			t, err := decodeTerms(raw)
			if err != nil {
				return nil, err
			}
			tot, err := ComputeTotals(t)
			if err != nil {
				return nil, err
			}
			return json.Marshal(struct {
				OrderID     string
				AmountCents int64
				Currency    string
			}{t.OrderID, tot.Total, t.Currency})
		},
		"checkout.reserve": func(raw json.RawMessage, _ int) ([]byte, error) {
			t, err := decodeTerms(raw)
			if err != nil {
				return nil, err
			}
			if t.PickupSlot == "" {
				return nil, fmt.Errorf("%w: no pickup slot", ErrPlanFails)
			}
			return json.Marshal(struct {
				OrderID    string
				Items      []Item
				PickupSlot string
			}{t.OrderID, t.Items, t.PickupSlot})
		},
		"checkout.ship": func(raw json.RawMessage, _ int) ([]byte, error) {
			t, err := decodeTerms(raw)
			if err != nil {
				return nil, err
			}
			if t.ShipTo == "" {
				return nil, fmt.Errorf("%w: no address", ErrPlanFails)
			}
			return json.Marshal(struct {
				OrderID string
				ShipTo  string
				Items   []Item
			}{t.OrderID, t.ShipTo, t.Items})
		},
	}
}
