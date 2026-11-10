TLA2TOOLS_VERSION ?= v1.8.0
TLA2TOOLS := tools/tla2tools.jar
TLAPM ?= tlapm
TLC := java -XX:+UseParallelGC -cp ../$(TLA2TOOLS) tlc2.TLC -workers auto -cleanup

.PHONY: test demo build tlc-quick tlc-full tlc-mutations tlaps clean

build:
	go build ./...

test:
	go vet ./...
	go test ./...

demo:
	go run ./cmd/demo
	go run ./cmd/demo -fork

$(TLA2TOOLS):
	mkdir -p tools
	curl -sSL -o $@ https://github.com/tlaplus/tlaplus/releases/download/$(TLA2TOOLS_VERSION)/tla2tools.jar

# Fast configs (seconds to a couple of minutes each).
tlc-quick: $(TLA2TOOLS)
	cd spec && $(TLC) -config FullHonest.cfg MC.tla
	cd spec && $(TLC) -config Checkout_Honest.cfg MCCheckout.tla
	cd spec && $(TLC) -config LogForkByzOp.cfg LogFork.tla
	cd spec && $(TLC) -config OracleByzOwner.cfg MCOracleByzOwner.tla
	cd spec && $(TLC) -config CensorByzOp.cfg MC.tla

# The main Byzantine configs (several minutes each on a laptop).
tlc-full: tlc-quick
	cd spec && $(TLC) -config Full1Byz.cfg MC.tla
	cd spec && $(TLC) -config Chain1Byz.cfg MCChain.tla
	cd spec && $(TLC) -config Checkout_Byz_merchant.cfg MCCheckout.tla
	cd spec && $(TLC) -config Checkout_Byz_carrier.cfg MCCheckout.tla

# Each mutant removes one protocol rule; TLC must find a violation in every one.
tlc-mutations: $(TLA2TOOLS)
	@for m in spec/mutations/mut*; do \
		out=$$(cd $$m && java -XX:+UseParallelGC -cp ../../../$(TLA2TOOLS) tlc2.TLC -workers auto -cleanup -config S.cfg MC.tla 2>&1); \
		if echo "$$out" | grep -q "is violated"; then echo "$$m: caught: $$(echo "$$out" | grep -m1 'is violated')"; \
		else echo "$$m: NOT CAUGHT"; exit 1; fi; \
	done

tlaps:
	cd spec && $(TLAPM) AccountableSagaProofs.tla

clean:
	rm -rf bin example spec/states spec/.tlacache
