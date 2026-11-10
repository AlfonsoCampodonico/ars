package translog

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"strconv"

	"github.com/AlfonsoCampodonico/ars/merkle"
)

// Handler serves a log over HTTP:
//
//	POST /entries              body = raw entry bytes -> Receipt
//	GET  /entries?from=N       -> []Leaf
//	GET  /checkpoint           -> latest Checkpoint
//	GET  /checkpoint?size=N    -> Checkpoint at size N
//	GET  /proof/consistency?from=M&to=N -> []hex
//	GET  /proof/inclusion?index=I&size=N -> []hex
func Handler(l API) http.Handler {
	mux := http.NewServeMux()
	mux.HandleFunc("POST /entries", func(w http.ResponseWriter, r *http.Request) {
		data, err := io.ReadAll(io.LimitReader(r.Body, 1<<20))
		if err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		reply(w)(l.Append(data))
	})
	mux.HandleFunc("GET /entries", func(w http.ResponseWriter, r *http.Request) {
		reply(w)(l.Entries(qint(r, "from")))
	})
	mux.HandleFunc("GET /checkpoint", func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Query().Has("size") {
			reply(w)(l.CheckpointAt(qint(r, "size")))
			return
		}
		reply(w)(l.Latest())
	})
	mux.HandleFunc("GET /proof/consistency", func(w http.ResponseWriter, r *http.Request) {
		p, err := l.ConsistencyProof(qint(r, "from"), qint(r, "to"))
		reply(w)(hexes(p), err)
	})
	mux.HandleFunc("GET /proof/inclusion", func(w http.ResponseWriter, r *http.Request) {
		p, err := l.InclusionProof(qint(r, "index"), qint(r, "size"))
		reply(w)(hexes(p), err)
	})
	return mux
}

func qint(r *http.Request, k string) uint64 {
	v, _ := strconv.ParseUint(r.URL.Query().Get(k), 10, 64)
	return v
}

func reply(w http.ResponseWriter) func(any, error) {
	return func(v any, err error) {
		if err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(v)
	}
}

func hexes(p []merkle.Hash) []string {
	out := make([]string, len(p))
	for i, h := range p {
		out[i] = fmt.Sprintf("%x", h[:])
	}
	return out
}

// Client talks to a Handler over HTTP and implements API.
type Client struct {
	Base string
	HTTP *http.Client
}

func (c *Client) http() *http.Client {
	if c.HTTP != nil {
		return c.HTTP
	}
	return http.DefaultClient
}

func (c *Client) get(path string, out any) error {
	resp, err := c.http().Get(c.Base + path)
	if err != nil {
		return err
	}
	return decode(resp, out)
}

func decode(resp *http.Response, out any) error {
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		b, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("translog: %s: %s", resp.Status, bytes.TrimSpace(b))
	}
	return json.NewDecoder(resp.Body).Decode(out)
}

func (c *Client) Append(data []byte) (Receipt, error) {
	var r Receipt
	resp, err := c.http().Post(c.Base+"/entries", "application/octet-stream", bytes.NewReader(data))
	if err != nil {
		return r, err
	}
	return r, decode(resp, &r)
}

func (c *Client) Entries(from uint64) ([]Leaf, error) {
	var out []Leaf
	return out, c.get(fmt.Sprintf("/entries?from=%d", from), &out)
}

func (c *Client) Latest() (Checkpoint, error) {
	var cp Checkpoint
	return cp, c.get("/checkpoint", &cp)
}

func (c *Client) CheckpointAt(size uint64) (Checkpoint, error) {
	var cp Checkpoint
	return cp, c.get(fmt.Sprintf("/checkpoint?size=%d", size), &cp)
}

func (c *Client) ConsistencyProof(from, to uint64) ([]merkle.Hash, error) {
	return c.proof(fmt.Sprintf("/proof/consistency?from=%d&to=%d", from, to))
}

func (c *Client) InclusionProof(index, size uint64) ([]merkle.Hash, error) {
	return c.proof(fmt.Sprintf("/proof/inclusion?index=%d&size=%d", index, size))
}

func (c *Client) proof(path string) ([]merkle.Hash, error) {
	var hs []string
	if err := c.get(path, &hs); err != nil {
		return nil, err
	}
	out := make([]merkle.Hash, len(hs))
	for i, s := range hs {
		h, err := decodeRoot(s)
		if err != nil {
			return nil, err
		}
		out[i] = h
	}
	return out, nil
}
