// Package keys loads and stores ed25519 keys as hex-encoded seeds.
package keys

import (
	"crypto/ed25519"
	"crypto/rand"
	"encoding/hex"
	"errors"
	"fmt"
	"os"
	"strings"
)

// Load reads a hex seed file.
func Load(path string) (ed25519.PrivateKey, error) {
	b, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	seed, err := hex.DecodeString(strings.TrimSpace(string(b)))
	if err != nil || len(seed) != ed25519.SeedSize {
		return nil, fmt.Errorf("%s: not a hex ed25519 seed", path)
	}
	return ed25519.NewKeyFromSeed(seed), nil
}

// Save writes key's seed as hex with owner-only permissions.
func Save(path string, key ed25519.PrivateKey) error {
	return os.WriteFile(path, []byte(hex.EncodeToString(key.Seed())+"\n"), 0o600)
}

// LoadOrCreate loads path, generating and saving a new key if it is missing.
func LoadOrCreate(path string) (ed25519.PrivateKey, error) {
	k, err := Load(path)
	if errors.Is(err, os.ErrNotExist) {
		_, k, err = ed25519.GenerateKey(rand.Reader)
		if err == nil {
			err = Save(path, k)
		}
	}
	return k, err
}
