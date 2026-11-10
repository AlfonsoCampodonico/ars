package protocol

import (
	"bytes"
	"encoding/json"
	"fmt"
	"slices"
	"sort"
	"time"

	"github.com/AlfonsoCampodonico/ars/translog"
)

// Stage of a step. Names match the TLA+ spec.
type Stage string

const (
	Pending   Stage = "pending"
	PlanPh    Stage = "plan"
	EffectPh  Stage = "effect"  // owner may attest
	RespondPh Stage = "respond" // beneficiary may still confirm or dispute
	Committed Stage = "committed"
	Aborted   Stage = "aborted"
	Disputed  Stage = "disputed" // the beneficiary disputes and no oracle can settle it
	Cancelled Stage = "cancelled"
)

// StepState is one step's derived state.
type StepState struct {
	Name           string    `json:"name"`
	Stage          Stage     `json:"stage"`
	Opened         time.Time `json:"opened,omitzero"`
	PlanDeadline   time.Time `json:"plan_deadline,omitzero"`
	AttestDeadline time.Time `json:"attest_deadline,omitzero"`
	EffectDeadline time.Time `json:"effect_deadline,omitzero"`
	Truth          string    `json:"truth"` // correct vote value (hash or ABORT)
	opened         bool
	decided        time.Time
}

// Evidence is publicly checkable proof that an org misbehaved.
type Evidence struct {
	Org    string  `json:"org"`
	Kind   string  `json:"kind"`
	Step   int     `json:"step"`
	Detail string  `json:"detail"`
	Proof  []Entry `json:"proof,omitempty"` // signed entries backing the claim
}

// Dispute is an unresolved owner/beneficiary contradiction on a step
// without an oracle: one of the two lied, the protocol can't tell which.
type Dispute struct {
	Step  int    `json:"step"`
	Owner string `json:"owner"`
	Benef string `json:"benef"`
}

// Censorship is an org (or oracle) saying the log operator refused one of
// its entries. Nobody can tell whether the operator or the claimant lied.
type Censorship struct {
	Step int    `json:"step"`
	Kind Kind   `json:"kind"`
	From string `json:"from"`
}

// Bond outcomes at settlement.
const (
	BondHeld     = "held"
	BondSlashed  = "slashed"
	BondFrozen   = "frozen"
	BondReturned = "returned"
)

// State is everything derivable from (definition, log, claims, now).
type State struct {
	Def          *SagaDef          `json:"-"`
	Now          time.Time         `json:"now"`
	Steps        []StepState       `json:"steps"`
	Aborted      bool              `json:"aborted"` // a step aborted: compensation runs
	Held         bool              `json:"held"`    // a step is disputed: nothing commits or unwinds
	EndedAt      time.Time         `json:"ended_at,omitzero"`
	Comp         string            `json:"compensation"` // none, open, respond, closed, held
	UndoDeadline time.Time         `json:"undo_deadline,omitzero"`
	CompDeadline time.Time         `json:"compensation_deadline,omitzero"`
	Finished     bool              `json:"finished"`
	Evidence     []Evidence        `json:"evidence"`
	Disputes     []Dispute         `json:"disputes"`
	Censored     []Censorship      `json:"censored"`
	Operator     []Evidence        `json:"operator_evidence"` // against the log operator
	Bonds        map[string]string `json:"bonds"`
	log          index             // entries on the log, in their final windows
	signed       index             // log plus credible claims: what each party filed
}

type ikey struct {
	kind Kind
	from string
	step int
}

type index map[ikey][]Entry

// window is (from, to], or [from, to] when inclusive. Plan windows include
// their opening instant so an org can vote the moment a step opens; later
// phases start strictly after the previous deadline.
type window struct {
	from, to  time.Time
	ok        bool
	inclusive bool
}

func (w window) has(t time.Time) bool {
	if !w.ok || t.After(w.to) {
		return false
	}
	return t.After(w.from) || (w.inclusive && t.Equal(w.from))
}

func minTime(a, b time.Time) time.Time {
	if b.Before(a) {
		return b
	}
	return a
}

// Entries accepted in the owner's sub-window vs until the end of the phase.
var respondKinds = []Kind{KConfirm, KDispute, KODone}
var compRespondKinds = []Kind{KUndoOk, KUndoDispute, KOUndone}

// accepted filters out entries the protocol ignores: wrong saga, bad
// signature, or a signer acting outside its role for that kind.
func accepted(def *SagaDef, e Entry) bool {
	if e.Saga != def.ID || e.Step < 0 || e.Step >= len(def.Steps) {
		return false
	}
	s := def.Steps[e.Step]
	switch e.Kind {
	case KVote, KReceipt:
		if !def.isOrg(e.From) {
			return false
		}
	case KEffect, KUndo:
		if e.From != s.Owner {
			return false
		}
	case KConfirm, KDispute, KUndoOk, KUndoDispute:
		if e.From != s.Benef {
			return false
		}
	case KODone, KOUndone:
		if s.Oracle == "" || e.From != s.Oracle {
			return false
		}
	default:
		return false
	}
	if e.Kind == KVote && e.Val == "" {
		return false
	}
	return e.Verify(def.key(e.From))
}

// Evaluate derives the saga state. It is deterministic: every org running
// it over the same log and claims at the same time gets the same answer.
// Outcomes depend on the log alone; claims only change who is blamed.
func Evaluate(def *SagaDef, plans Plans, recs []Record, claims []Claim, now time.Time) (*State, error) {
	if err := def.Validate(); err != nil {
		return nil, err
	}
	n := len(def.Steps)
	st := &State{Def: def, Now: now, Steps: make([]StepState, n), Comp: "none", Bonds: map[string]string{}}

	byStep := make([][]Record, n)
	for _, r := range recs {
		if accepted(def, r.Entry) {
			byStep[r.Entry.Step] = append(byStep[r.Entry.Step], r)
		}
	}
	for i, s := range def.Steps {
		v, err := plans.Run(s.Plan, def.Terms, i)
		if err != nil {
			return nil, fmt.Errorf("step %d: %w", i, err)
		}
		st.Steps[i] = StepState{Name: s.Name, Stage: Pending, Truth: v}
	}

	// Pass 1: decide each step from its own windows, in topological order.
	planWin := func(i int) window {
		s := st.Steps[i]
		return window{s.Opened, s.PlanDeadline, s.opened, true}
	}
	attWin := func(i int) window {
		s := st.Steps[i]
		return window{s.PlanDeadline, s.AttestDeadline, s.opened, false}
	}
	effWin := func(i int) window {
		s := st.Steps[i]
		return window{s.PlanDeadline, s.EffectDeadline, s.opened, false}
	}
	for i, sd := range def.Steps {
		ss := &st.Steps[i]
		open, ready := def.Start, true
		for _, d := range sd.Deps {
			if st.Steps[d].Stage != Committed {
				ready = false
				break
			}
			if st.Steps[d].decided.After(open) {
				open = st.Steps[d].decided
			}
		}
		if !ready || now.Before(open) {
			continue // pending
		}
		ss.opened, ss.Opened = true, open
		ss.PlanDeadline = open.Add(sd.PlanDur.Duration)
		ss.AttestDeadline = ss.PlanDeadline.Add(sd.EffectDur.Duration)
		ss.EffectDeadline = ss.AttestDeadline.Add(sd.RespondDur.Duration)
		if !now.After(ss.PlanDeadline) {
			ss.Stage = PlanPh
			continue
		}
		ix := buildIndex(byStep[i], map[Kind]window{KVote: planWin(i)})
		if !ix.planPassed(def, i) {
			ss.Stage, ss.decided = Aborted, ss.PlanDeadline
			continue
		}
		if !now.After(ss.AttestDeadline) {
			ss.Stage = EffectPh
			continue
		}
		if !now.After(ss.EffectDeadline) {
			ss.Stage = RespondPh
			continue
		}
		w := effWin(i)
		ix = buildIndex(byStep[i], map[Kind]window{KEffect: attWin(i), KConfirm: w, KDispute: w, KODone: w})
		switch {
		case ix.effectOK(def, i):
			ss.Stage, ss.decided = Committed, ss.EffectDeadline
		case ix.effectDisputed(def, i):
			ss.Stage, ss.decided = Disputed, ss.EffectDeadline
		default:
			ss.Stage, ss.decided = Aborted, ss.EffectDeadline
		}
	}

	// The earliest abort or dispute ends the saga; everything not decided by
	// then is cancelled. On a tie the dispute wins: holding moves no money.
	var end *StepState
	for i := range st.Steps {
		ss := &st.Steps[i]
		if ss.Stage != Aborted && ss.Stage != Disputed {
			continue
		}
		if end == nil || ss.decided.Before(end.decided) || (ss.decided.Equal(end.decided) && ss.Stage == Disputed) {
			end = ss
		}
	}
	if end != nil {
		st.Aborted, st.Held, st.EndedAt = end.Stage == Aborted, end.Stage == Disputed, end.decided
		for i := range st.Steps {
			ss := &st.Steps[i]
			decided := ss.Stage == Committed || ss.Stage == Aborted || ss.Stage == Disputed
			if !decided || ss.decided.After(st.EndedAt) || st.Held && ss.Stage == Aborted {
				ss.Stage = Cancelled
			}
		}
	}
	switch {
	case st.Held:
		st.Comp = "held"
	case st.Aborted:
		st.UndoDeadline = st.EndedAt.Add(def.CompDur.Duration)
		st.CompDeadline = st.UndoDeadline.Add(def.CompRespondDur.Duration)
		switch {
		case !now.After(st.UndoDeadline):
			st.Comp = "open"
		case !now.After(st.CompDeadline):
			st.Comp = "respond"
		default:
			st.Comp = "closed"
		}
	}

	// Pass 2: final windows (cut where the saga ended) for evidence and obligations.
	wins := func(i int) map[Kind]window {
		pw, aw, ew := planWin(i), attWin(i), effWin(i)
		if end != nil {
			pw.to, aw.to, ew.to = minTime(pw.to, st.EndedAt), minTime(aw.to, st.EndedAt), minTime(ew.to, st.EndedAt)
		}
		uw := window{st.EndedAt, st.UndoDeadline, st.Aborted, false}
		cw := window{st.EndedAt, st.CompDeadline, st.Aborted, false}
		m := map[Kind]window{KVote: pw, KEffect: aw, KReceipt: uw, KUndo: uw}
		for _, k := range respondKinds {
			m[k] = ew
		}
		for _, k := range compRespondKinds {
			m[k] = cw
		}
		return m
	}
	st.log = index{}
	for i := range def.Steps {
		for k, v := range buildIndex(byStep[i], wins(i)) {
			st.log[k] = v
		}
	}
	st.addClaims(claims, wins)
	st.collectEvidence()

	allCommitted := true
	for _, ss := range st.Steps {
		allCommitted = allCommitted && ss.Stage == Committed
	}
	st.Finished = allCommitted || st.Comp == "closed" || st.Held
	for _, o := range def.Orgs {
		st.Bonds[o.Name] = BondHeld
	}
	if st.Finished {
		accused := st.Accused()
		for _, o := range def.Orgs {
			switch {
			case accused[o.Name]:
				st.Bonds[o.Name] = BondSlashed
			case st.inDispute(o.Name):
				st.Bonds[o.Name] = BondFrozen
			default:
				st.Bonds[o.Name] = BondReturned
			}
		}
	}
	return st, nil
}

// addClaims builds the signed view: the log plus every credible claim. A
// claim counts when it is validly signed, in the claimant's role, filed
// inside the window its entry belongs to, and not settled by the log. An
// entry is a broken promise (evidence against the operator) if any claim
// for it carries a receipt the log doesn't honor; otherwise it is an
// unresolved censorship dispute. Claims are sorted first, so the result
// doesn't depend on the order gossip delivered them in.
func (st *State) addClaims(claims []Claim, wins func(int) map[Kind]window) {
	def := st.Def
	st.signed = index{}
	for k, v := range st.log {
		st.signed[k] = v
	}
	claims = slices.Clone(claims)
	slices.SortFunc(claims, func(a, b Claim) int { return bytes.Compare(a.Sig, b.Sig) })
	type verdict struct {
		entry   Entry
		receipt *translog.Receipt
	}
	found := map[ikey]*verdict{}
	var keys []ikey
	for _, c := range claims {
		e := c.Entry
		if !accepted(def, e) || !c.Verify(def.key(e.From)) {
			continue
		}
		w := wins(e.Step)[e.Kind]
		k := ikey{e.Kind, e.From, e.Step}
		if !w.has(c.Time) || st.log.has(e.Kind, e.From, e.Step) {
			continue
		}
		st.signed[k] = append(st.signed[k], e)
		v := found[k]
		if v == nil {
			v = &verdict{entry: e}
			found[k] = v
			keys = append(keys, k)
		}
		// An honored receipt would have put the entry on the log inside its
		// window, which was skipped above: a valid receipt here is broken.
		data, _ := json.Marshal(e)
		if r := c.Receipt; v.receipt == nil && r != nil && r.Verify(def.LogKey) && r.For(data) && w.has(r.Time) {
			v.entry, v.receipt = e, r
		}
	}
	for _, k := range keys {
		v := found[k]
		if v.receipt == nil {
			st.Censored = append(st.Censored, Censorship{k.step, k.kind, k.from})
			continue
		}
		st.Operator = append(st.Operator, Evidence{"log operator", "broken promise", k.step,
			fmt.Sprintf("signed a receipt for %s's %s at index %d, then didn't keep it", k.from, k.kind, v.receipt.Index),
			[]Entry{v.entry}})
	}
}

func buildIndex(recs []Record, wins map[Kind]window) index {
	ix := index{}
	for _, r := range recs {
		if w, ok := wins[r.Entry.Kind]; ok && w.has(r.Time) {
			k := ikey{r.Entry.Kind, r.Entry.From, r.Entry.Step}
			ix[k] = append(ix[k], r.Entry)
		}
	}
	return ix
}

func (ix index) has(k Kind, from string, step int) bool { return len(ix[ikey{k, from, step}]) > 0 }
func (ix index) first(k Kind, from string, step int) []Entry {
	if e := ix[ikey{k, from, step}]; len(e) > 0 {
		return e[:1]
	}
	return nil
}

func (ix index) planPassed(def *SagaDef, step int) bool {
	vals := map[string]bool{}
	for _, o := range def.Orgs {
		for _, e := range ix[ikey{KVote, o.Name, step}] {
			vals[e.Val] = true
		}
	}
	if len(vals) != 1 || vals[Abort] {
		return false // conflicting votes, or a (claimed) failure
	}
	for _, o := range def.Orgs {
		if !ix.has(KVote, o.Name, step) {
			return false // not unanimous
		}
	}
	return true
}

func (ix index) effectOK(def *SagaDef, step int) bool {
	s := def.Steps[step]
	if !ix.has(KEffect, s.Owner, step) {
		return false
	}
	if s.Oracle != "" {
		return ix.has(KODone, s.Oracle, step)
	}
	return ix.has(KConfirm, s.Benef, step) && !ix.has(KDispute, s.Benef, step)
}

// effectDisputed: the beneficiary disputes an attested effect no oracle covers.
func (ix index) effectDisputed(def *SagaDef, step int) bool {
	s := def.Steps[step]
	return s.Oracle == "" && ix.has(KEffect, s.Owner, step) && ix.has(KDispute, s.Benef, step)
}

// Filed reports whether the signer filed an entry of this kind for step in
// its final window, on the log or as a credible censorship claim.
func (st *State) Filed(k Kind, from string, step int) bool { return st.signed.has(k, from, step) }

// PlanPassed reports whether step's plan has a clean commit certificate.
func (st *State) PlanPassed(step int) bool { return st.log.planPassed(st.Def, step) }

func (st *State) attestFiled(i int) bool { return st.Filed(KEffect, st.Def.Steps[i].Owner, i) }

// BenefDue: the beneficiary must confirm or dispute step i's effect, once
// the attestation is on the log. On oracle steps the oracle decides and the
// beneficiary has no duty.
func (st *State) BenefDue(i int) bool {
	s := st.Def.Steps[i]
	return s.Oracle == "" && st.log.has(KEffect, s.Owner, i)
}

// UndoBenefDue: the beneficiary must check the owner's logged undo of step i.
func (st *State) UndoBenefDue(i int) bool {
	s := st.Def.Steps[i]
	return s.Oracle == "" && st.log.has(KUndo, s.Owner, i)
}

// OwesReceipt: every org must post a receipt for committed step i.
func (st *State) OwesReceipt(i int) bool { return st.Aborted && st.Steps[i].Stage == Committed }

// OwesUndo: the owner must undo step i's attested effect, unless the step
// is a pivot, whose effect can't be undone.
func (st *State) OwesUndo(i int) bool {
	return st.Aborted && !st.Def.Steps[i].Pivot && st.attestFiled(i)
}

func (st *State) closed(i int) bool {
	s := st.Steps[i].Stage
	return s == Committed || s == Aborted || s == Disputed
}

func (st *State) planClosed(i int) bool {
	s := st.Steps[i].Stage
	return s == EffectPh || s == RespondPh || st.closed(i)
}

func (st *State) effectClosed(i int) bool { return st.closed(i) && st.PlanPassed(i) }

func (st *State) collectEvidence() {
	def, ix := st.Def, st.signed
	add := func(o, kind string, step int, detail string, proof ...Entry) {
		st.Evidence = append(st.Evidence, Evidence{o, kind, step, detail, proof})
	}
	closed := st.Comp == "closed"
	for _, org := range def.Orgs {
		o := org.Name
		for i, s := range def.Steps {
			truth := st.Steps[i].Truth
			votes := ix[ikey{KVote, o, i}]
			byVal := map[string]Entry{}
			for _, v := range votes {
				byVal[v.Val] = v
			}
			if len(byVal) > 1 {
				var p []Entry
				for _, v := range byVal {
					p = append(p, v)
				}
				sort.Slice(p, func(a, b int) bool { return p[a].Val < p[b].Val })
				add(o, "equivocation", i, "signed two different plan votes", p[:2]...)
			}
			for _, v := range votes {
				switch {
				case v.Val == Abort && truth != Abort:
					add(o, "unjustified veto", i, "voted ABORT but the plan re-executes fine", v)
				case v.Val != Abort && truth == Abort:
					add(o, "wrong result", i, "endorsed a plan that fails on re-execution", v)
				case v.Val != Abort && v.Val != truth:
					add(o, "wrong result", i, "vote doesn't match re-execution", v)
				}
			}
			if st.planClosed(i) && len(votes) == 0 {
				add(o, "silent voter", i, "no vote before the plan deadline")
			}
			if o == s.Owner {
				if st.effectClosed(i) && !st.attestFiled(i) {
					add(o, "silent owner", i, "no effect attestation before the deadline")
				}
				if s.Oracle != "" && st.effectClosed(i) && st.attestFiled(i) && !ix.has(KODone, s.Oracle, i) {
					add(o, "false attestation", i, "oracle never saw the claimed effect", ix.first(KEffect, o, i)...)
				}
				if s.Oracle != "" && closed && ix.has(KUndo, o, i) && !ix.has(KOUndone, s.Oracle, i) {
					add(o, "false undo", i, "oracle never saw the claimed undo", ix.first(KUndo, o, i)...)
				}
				if closed && st.OwesUndo(i) && !ix.has(KUndo, o, i) {
					add(o, "default", i, "attested effect never undone")
				}
			}
			if o == s.Benef {
				if ix.has(KConfirm, o, i) && ix.has(KDispute, o, i) {
					add(o, "equivocation", i, "both confirmed and disputed the effect",
						append(ix.first(KConfirm, o, i), ix.first(KDispute, o, i)...)...)
				}
				if ix.has(KUndoOk, o, i) && ix.has(KUndoDispute, o, i) {
					add(o, "equivocation", i, "both confirmed and disputed the undo",
						append(ix.first(KUndoOk, o, i), ix.first(KUndoDispute, o, i)...)...)
				}
				if st.effectClosed(i) && st.BenefDue(i) && !ix.has(KConfirm, o, i) && !ix.has(KDispute, o, i) {
					add(o, "silent beneficiary", i, "no confirm/dispute before the deadline")
				}
				if s.Oracle != "" && ix.has(KDispute, o, i) && ix.has(KODone, s.Oracle, i) {
					add(o, "false dispute", i, "disputed an effect the oracle confirmed",
						append(ix.first(KDispute, o, i), ix.first(KODone, s.Oracle, i)...)...)
				}
				if s.Oracle != "" && ix.has(KUndoDispute, o, i) && ix.has(KOUndone, s.Oracle, i) {
					add(o, "false dispute", i, "disputed an undo the oracle confirmed",
						append(ix.first(KUndoDispute, o, i), ix.first(KOUndone, s.Oracle, i)...)...)
				}
				if closed && st.UndoBenefDue(i) && !ix.has(KUndoOk, o, i) && !ix.has(KUndoDispute, o, i) {
					add(o, "default", i, "never checked the owner's undo")
				}
			}
			if closed && st.OwesReceipt(i) && !ix.has(KReceipt, o, i) {
				add(o, "default", i, "no compensation receipt")
			}
		}
	}
	for i, s := range def.Steps {
		if s.Oracle == "" && (st.log.has(KDispute, s.Benef, i) || st.log.has(KUndoDispute, s.Benef, i)) {
			st.Disputes = append(st.Disputes, Dispute{i, s.Owner, s.Benef})
		}
	}
}

// Accused is the set of orgs named by individual evidence.
func (st *State) Accused() map[string]bool {
	out := map[string]bool{}
	for _, e := range st.Evidence {
		out[e.Org] = true
	}
	return out
}

func (st *State) inDispute(o string) bool {
	for _, d := range st.Disputes {
		if d.Owner == o || d.Benef == o {
			return true
		}
	}
	for _, c := range st.Censored {
		if c.From == o {
			return true
		}
	}
	return false
}
