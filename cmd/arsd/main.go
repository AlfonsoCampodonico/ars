// Command arsd is an org's ARS sidecar. It holds the org's signing key,
// votes and posts receipts on its own, and serves MCP tools over stdio so
// the org's agent can report real-world side effects. The agent can never
// sign arbitrary statements or choose a vote.
//
//	arsd -def saga.json -org merchant -key merchant.key -log http://localhost:8070
package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"os"
	"time"

	"github.com/modelcontextprotocol/go-sdk/mcp"

	"github.com/AlfonsoCampodonico/ars/keys"
	"github.com/AlfonsoCampodonico/ars/protocol"
	"github.com/AlfonsoCampodonico/ars/sidecar"
	"github.com/AlfonsoCampodonico/ars/translog"
)

type stepIn struct {
	Step int `json:"step" jsonschema:"saga step index, as listed by saga_status"`
}

type attestIn struct {
	Step int    `json:"step" jsonschema:"saga step index"`
	Ref  string `json:"ref" jsonschema:"external reference proving the action, e.g. charge ID, booking ID, tracking number"`
}

type observeIn struct {
	Step     int    `json:"step" jsonschema:"saga step index"`
	Happened bool   `json:"happened" jsonschema:"true only if you independently verified it really happened"`
	Note     string `json:"note,omitempty" jsonschema:"what you checked"`
}

type ack struct {
	OK      bool   `json:"ok"`
	Message string `json:"message"`
}

func main() {
	defPath := flag.String("def", "saga.json", "saga definition")
	org := flag.String("org", "", "this org's name in the saga")
	keyPath := flag.String("key", "", "this org's key file (hex seed)")
	logURL := flag.String("log", "http://localhost:8070", "transparency log URL")
	tick := flag.Duration("tick", 2*time.Second, "how often to vote and post receipts")
	flag.Parse()
	log.SetOutput(os.Stderr) // stdout belongs to MCP

	raw, err := os.ReadFile(*defPath)
	if err != nil {
		log.Fatal(err)
	}
	var def protocol.SagaDef
	if err := json.Unmarshal(raw, &def); err != nil {
		log.Fatal(err)
	}
	if err := def.Validate(); err != nil {
		log.Fatal(err)
	}
	key, err := keys.Load(*keyPath)
	if err != nil {
		log.Fatal(err)
	}
	car := &sidecar.Sidecar{Org: *org, Key: key, Def: &def, Plans: protocol.CheckoutPlans(),
		Log: &translog.Client{Base: *logURL}}

	go func() {
		for range time.Tick(*tick) {
			if _, err := car.Tick(); err != nil {
				log.Printf("tick: %v", err)
			}
		}
	}()

	srv := mcp.NewServer(&mcp.Implementation{Name: "ars-sidecar", Version: "0.1.0"}, &mcp.ServerOptions{
		Instructions: fmt.Sprintf("You act for %q in saga %q. The sidecar votes and posts receipts automatically. "+
			"Call saga_status to see your tasks. Only report side effects you actually performed or independently "+
			"verified: every report is signed by your organization and anything false becomes public evidence against it.",
			*org, def.ID),
	})

	mcp.AddTool(srv, &mcp.Tool{Name: "saga_status",
		Description: "Current saga state from the log: each step's stage and deadlines, evidence, disputes, bonds, and your outstanding tasks."},
		func(ctx context.Context, _ *mcp.CallToolRequest, _ struct{}) (*mcp.CallToolResult, any, error) {
			st, err := car.State()
			if err != nil {
				return nil, nil, err
			}
			todos, err := car.Tick()
			if err != nil {
				return nil, nil, err
			}
			return nil, map[string]any{"org": *org, "state": st, "your_tasks": todos}, nil
		})

	report := func(name, desc string, f func(observeIn) error) {
		mcp.AddTool(srv, &mcp.Tool{Name: name, Description: desc},
			func(ctx context.Context, _ *mcp.CallToolRequest, in observeIn) (*mcp.CallToolResult, ack, error) {
				if err := f(in); err != nil {
					return nil, ack{false, err.Error()}, nil
				}
				return nil, ack{true, "signed and posted to the log"}, nil
			})
	}
	attest := func(name, desc string, f func(attestIn) error) {
		mcp.AddTool(srv, &mcp.Tool{Name: name, Description: desc},
			func(ctx context.Context, _ *mcp.CallToolRequest, in attestIn) (*mcp.CallToolResult, ack, error) {
				if err := f(in); err != nil {
					return nil, ack{false, err.Error()}, nil
				}
				return nil, ack{true, "signed and posted to the log"}, nil
			})
	}
	attest("attest_effect", "As a step's owner: report that you PERFORMED its side effect (after doing it).",
		func(in attestIn) error { return car.AttestEffect(in.Step, in.Ref) })
	report("observe_effect", "As a step's beneficiary: report whether the owner's claimed effect really happened, after checking independently.",
		func(in observeIn) error { return car.ObserveEffect(in.Step, in.Happened, in.Note) })
	attest("attest_undo", "As a step's owner during compensation: report that you UNDID its side effect (refund, cancellation...).",
		func(in attestIn) error { return car.AttestUndo(in.Step, in.Ref) })
	report("observe_undo", "As a step's beneficiary during compensation: report whether the undo really happened.",
		func(in observeIn) error { return car.ObserveUndo(in.Step, in.Happened, in.Note) })

	if err := srv.Run(context.Background(), &mcp.StdioTransport{}); err != nil {
		log.Fatal(err)
	}
}
