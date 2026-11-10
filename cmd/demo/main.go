// Command demo runs the checkout scenarios in-process and prints what the
// log shows, the evidence, and how bonds settle. It can also demonstrate
// log-fork detection and write an example setup for arslog + arsd.
//
//	demo                      # all scenarios
//	demo -scenario carrier-lies
//	demo -fork                # equivocating log operator
//	demo -example ./example   # saga.json + keys for running arsd for real
package main

import (
	"crypto/ed25519"
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/AlfonsoCampodonico/ars/keys"
	"github.com/AlfonsoCampodonico/ars/protocol"
	"github.com/AlfonsoCampodonico/ars/sim"
	"github.com/AlfonsoCampodonico/ars/translog"
)

func main() {
	only := flag.String("scenario", "", "run one scenario by name")
	verbose := flag.Bool("v", false, "print the full event trace")
	fork := flag.Bool("fork", false, "demonstrate log-fork detection")
	example := flag.String("example", "", "write example saga.json and keys into this directory")
	flag.Parse()

	switch {
	case *fork:
		forkDemo()
		return
	case *example != "":
		if err := writeExample(*example); err != nil {
			log.Fatal(err)
		}
		return
	}
	for _, sc := range sim.Scenarios() {
		if *only != "" && sc.Name != *only {
			continue
		}
		run(sc, *verbose)
	}
}

func run(sc sim.Scenario, verbose bool) {
	fmt.Printf("\n=== %s ===\n%s\n\n", sc.Name, sc.Story)
	w := sc.Build()
	st := w.Run(6 * time.Hour)
	for _, line := range w.Trace {
		if verbose || !strings.Contains(line, "log says") {
			fmt.Println("  " + line)
		}
	}
	fmt.Println("\n  Steps:")
	for _, s := range st.Steps {
		fmt.Printf("    %-11s %s\n", s.Name, s.Stage)
	}
	if st.Aborted {
		fmt.Printf("  Saga aborted at %s; compensation %s\n", st.EndedAt.Format("15:04"), st.Comp)
	}
	if st.Held {
		fmt.Printf("  Saga held at %s: disputed, nothing commits or unwinds until resolved externally\n", st.EndedAt.Format("15:04"))
	}
	fmt.Printf("  Buyer's card: %s\n", map[string]string{"no": "never charged", "done": "CHARGED", "undone": "charged then refunded"}[w.Observed(sim.StepPay)])
	if len(st.Evidence) == 0 && len(st.Operator) == 0 {
		fmt.Println("  Evidence: none")
	}
	for _, e := range st.Evidence {
		fmt.Printf("  Evidence: %-8s %-18s step %d  %s (%d signed entries attached)\n", e.Org, e.Kind, e.Step, e.Detail, len(e.Proof))
	}
	for _, d := range st.Disputes {
		fmt.Printf("  Dispute:  step %d, %s vs %s (no oracle; resolve externally)\n", d.Step, d.Owner, d.Benef)
	}
	for _, c := range st.Censored {
		fmt.Printf("  Dispute:  step %d, %s vs the log operator (%s refused; resolve externally)\n", c.Step, c.From, c.Kind)
	}
	for _, e := range st.Operator {
		fmt.Printf("  Evidence: %s %s step %d  %s\n", e.Org, e.Kind, e.Step, e.Detail)
	}
	fmt.Printf("  Bonds:    buyer=%s merchant=%s carrier=%s\n",
		st.Bonds[sim.Buyer], st.Bonds[sim.Merchant], st.Bonds[sim.Carrier])
	if cp, err := w.Log.Latest(); err == nil {
		fmt.Printf("  Log:      %d entries, root %s…\n", cp.Size, cp.Root[:16])
	}
}

func forkDemo() {
	fmt.Println("\n=== log fork ===")
	fmt.Println("The log operator shows the buyer one history and the merchant another.")
	key := sim.Key("log-operator")
	pub := key.Public().(ed25519.PublicKey)
	clock := time.Date(2026, 11, 8, 9, 0, 0, 0, time.UTC)
	honest := translog.New("ars-demo-log", key, func() time.Time { return clock })
	honest.Append([]byte(`{"step":0,"kind":"vote"}`))
	evil := honest.Fork()
	honest.Append([]byte(`{"step":3,"kind":"confirm"} -- shown to the merchant`))
	evil.Append([]byte(`{"step":3,"kind":"dispute"} -- shown to the buyer`))
	a, _ := honest.Latest()
	b, _ := evil.Latest()
	fmt.Printf("  merchant's view: size %d root %s…\n", a.Size, a.Root[:16])
	fmt.Printf("  buyer's view:    size %d root %s…\n", b.Size, b.Root[:16])
	p, err := translog.CompareViews(pub, honest, evil)
	if err != nil {
		log.Fatal(err)
	}
	if p != nil {
		fmt.Printf("  Gossip: FORK PROOF -- two checkpoints at size %d, both signed by the operator, different roots.\n", p.A.Size)
		fmt.Printf("  Verifiable by anyone with the operator's key: %v\n", p.Valid(pub))
		fmt.Println("  Per LogFork.tla: orgs that see a conflict before finality abort and compensate.")
	}
}

func writeExample(dir string) error {
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return err
	}
	names := []string{sim.Buyer, sim.Merchant, sim.Carrier, sim.PSPName, "log"}
	pubs := map[string]ed25519.PublicKey{}
	for _, n := range names {
		k, err := keys.LoadOrCreate(filepath.Join(dir, n+".key"))
		if err != nil {
			return err
		}
		pubs[n] = k.Public().(ed25519.PublicKey)
	}
	def := sim.CheckoutDef(time.Now().Add(time.Minute).Truncate(time.Second), sim.CheckoutTerms())
	for i := range def.Orgs {
		def.Orgs[i].PubKey = pubs[def.Orgs[i].Name]
	}
	for i := range def.Oracles {
		def.Oracles[i].PubKey = pubs[def.Oracles[i].Name]
	}
	def.LogOrigin, def.LogKey = "ars-log", pubs["log"] // arslog -key <dir>/log.key (default origin)
	b, err := json.MarshalIndent(def, "", "  ")
	if err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(dir, "saga.json"), b, 0o644); err != nil {
		return err
	}
	var t protocol.CheckoutTerms
	_ = json.Unmarshal(def.Terms, &t)
	tot, _ := protocol.ComputeTotals(t)
	fmt.Printf("wrote %s/saga.json (starts %s, total %d.%02d %s) and keys for %s\n",
		dir, def.Start.Format(time.RFC3339), tot.Total/100, tot.Total%100, t.Currency, strings.Join(names, ", "))
	return nil
}
