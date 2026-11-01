.PHONY: install run demo build audit bench test clean

# Install the pinned Lean toolchain (via elan) and build everything.
install:
	@command -v elan >/dev/null 2>&1 || curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
	elan toolchain list | grep -q "$$(cat lean-toolchain)" || elan toolchain install $$(cat lean-toolchain)
	lake build
	cd web && npm install --no-audit --no-fund
	node web/samples/fetch.mjs

# Run the app: open http://localhost:8765 in Chrome.
# Set ANTHROPIC_API_KEY to have Claude write the calls (otherwise built-in calls are used).
run:
	@lake build sound-and-complete
	@(sleep 1 && (open http://localhost:8765 2>/dev/null || xdg-open http://localhost:8765 2>/dev/null || true)) &
	node web/server.js

# Terminal demo of the Lean core.
demo:
	lake exe sound-and-complete

# Browser-side tests (audio pipeline, call generator).
test:
	node --test web/*.test.mjs web/audio/*.test.mjs

build:
	lake build

# Print what each main theorem depends on, and which axioms its proof uses.
# `sorryAx` in the output means a proof is not finished.
audit:
	lake build SoundAndComplete.Audit
	lake env lean SoundAndComplete/Report.lean

# Time the answer search on a few rule sets (compiled).
bench:
	lake build bench
	.lake/build/bin/bench

clean:
	lake clean
