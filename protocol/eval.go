package protocol

import (
	"fmt"
	"sort"
	"time"
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

// Bond outcomes at settlement.
const (
	BondHeld     = "held"
	BondSlashed  = "slashed"
	BondFrozen   = "frozen"
	BondReturned = "returned"
)

// State is everything derivable from (definition, log, now).
type State struct {
	Def          *SagaDef          `json:"-"`
	Now          time.Time         `json:"now"`
	Steps        []StepState       `json:"steps"`
	Aborted      bool              `json:"aborted"`
	AbortAt      time.Time         `json:"abort_at,omitzero"`
	Comp         string            `json:"compensation"` // none, open, respond, closed
	UndoDeadline time.Time         `json:"undo_deadline,omitzero"`
	CompDeadline time.Time         `json:"compensation_deadline,omitzero"`
	Finished     bool              `json:"finished"`
	Evidence     []Evidence        `json:"evidence"`
	Disputes     []Dispute         `json:"disputes"`
	Bonds        map[string]string `json:"bonds"`
	ix           index
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
// it over the same log at the same time gets the same answer.
func Evaluate(def *SagaDef, plans Plans, recs []Record, now time.Time) (*State, error) {
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
		if ix.effectOK(def, i) {
			ss.Stage, ss.decided = Committed, ss.EffectDeadline
		} else {
			ss.Stage, ss.decided = Aborted, ss.EffectDeadline
		}
	}

	// The earliest abort aborts the saga; everything not decided by then is cancelled.
	for _, ss := range st.Steps {
		if ss.Stage == Aborted && (!st.Aborted || ss.decided.Before(st.AbortAt)) {
			st.Aborted, st.AbortAt = true, ss.decided
		}
	}
	if st.Aborted {
		for i := range st.Steps {
			ss := &st.Steps[i]
			decided := ss.Stage == Committed || ss.Stage == Aborted
			if !decided || ss.decided.After(st.AbortAt) {
				ss.Stage = Cancelled
			}
		}
		st.UndoDeadline = st.AbortAt.Add(def.CompDur.Duration)
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

	// Pass 2: final windows (cut at the abort) for evidence and obligations.
	all := index{}
	for i := range def.Steps {
		pw, aw, ew := planWin(i), attWin(i), effWin(i)
		if st.Aborted {
			pw.to, aw.to, ew.to = minTime(pw.to, st.AbortAt), minTime(aw.to, st.AbortAt), minTime(ew.to, st.AbortAt)
		}
		uw := window{st.AbortAt, st.UndoDeadline, st.Aborted, false}
		cw := window{st.AbortAt, st.CompDeadline, st.Aborted, false}
		wins := map[Kind]window{KVote: pw, KEffect: aw, KReceipt: uw, KUndo: uw}
		for _, k := range respondKinds {
			wins[k] = ew
		}
		for _, k := range compRespondKinds {
			wins[k] = cw
		}
		for k, v := range buildIndex(byStep[i], wins) {
			all[k] = v
		}
	}
	st.ix = all
	st.collectEvidence()

	allCommitted := true
	for _, ss := range st.Steps {
		allCommitted = allCommitted && ss.Stage == Committed
	}
	st.Finished = allCommitted || st.Comp == "closed"
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

// Has reports whether an entry of this kind/signer/step counts in the
// current final windows.
func (st *State) Has(k Kind, from string, step int) bool { return st.ix.has(k, from, step) }

// PlanPassed reports whether step's plan has a clean commit certificate.
func (st *State) PlanPassed(step int) bool { return st.ix.planPassed(st.Def, step) }

func (st *State) attested(i int) bool {
	return st.ix.has(KEffect, st.Def.Steps[i].Owner, i)
}

// BenefDue: the beneficiary must confirm or dispute step i's effect. On
// oracle steps the oracle decides and the beneficiary has no duty.
func (st *State) BenefDue(i int) bool {
	return st.Def.Steps[i].Oracle == "" && st.attested(i)
}

// UndoBenefDue: the beneficiary must check the owner's undo of step i.
func (st *State) UndoBenefDue(i int) bool {
	s := st.Def.Steps[i]
	return s.Oracle == "" && st.ix.has(KUndo, s.Owner, i)
}

// OwesReceipt: every org must post a receipt for committed step i.
func (st *State) OwesReceipt(i int) bool { return st.Aborted && st.Steps[i].Stage == Committed }

// OwesUndo: the owner must undo step i's attested effect.
func (st *State) OwesUndo(i int) bool { return st.Aborted && st.attested(i) }

func (st *State) planClosed(i int) bool {
	switch st.Steps[i].Stage {
	case EffectPh, RespondPh, Committed, Aborted:
		return true
	}
	return false
}

func (st *State) effectClosed(i int) bool {
	s := st.Steps[i].Stage
	return (s == Committed || s == Aborted) && st.PlanPassed(i)
}

func (st *State) collectEvidence() {
	def, ix := st.Def, st.ix
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
				if st.effectClosed(i) && !st.attested(i) {
					add(o, "silent owner", i, "no effect attestation before the deadline")
				}
				if s.Oracle != "" && st.effectClosed(i) && st.attested(i) && !ix.has(KODone, s.Oracle, i) {
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
		if s.Oracle == "" && (ix.has(KDispute, s.Benef, i) || ix.has(KUndoDispute, s.Benef, i)) {
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
	return false
}
