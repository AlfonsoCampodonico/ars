// Command arslog runs a transparency log over HTTP.
//
//	arslog -addr :8070 -key log.key
package main

import (
	"crypto/ed25519"
	"encoding/hex"
	"flag"
	"fmt"
	"log"
	"net/http"

	"ars/keys"
	"ars/translog"
)

func main() {
	addr := flag.String("addr", ":8070", "listen address")
	keyPath := flag.String("key", "log.key", "operator key file (hex seed; created if missing)")
	origin := flag.String("origin", "ars-log", "log origin name")
	flag.Parse()

	key, err := keys.LoadOrCreate(*keyPath)
	if err != nil {
		log.Fatal(err)
	}
	l := translog.New(*origin, key, nil)
	fmt.Printf("arslog %q listening on %s\noperator public key: %s\n",
		*origin, *addr, hex.EncodeToString(key.Public().(ed25519.PublicKey)))
	log.Fatal(http.ListenAndServe(*addr, translog.Handler(l)))
}
