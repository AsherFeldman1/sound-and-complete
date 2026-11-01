#!/usr/bin/env bash
# Run `lake check` and `lake comparator` in a Linux container (they need the
# Linux `bwrap` sandbox, so they cannot run directly on macOS).
# Usage: comparator/run.sh [--paranoid]
set -euo pipefail
cd "$(dirname "$0")/.."
docker build -q -t sac-comparator comparator >/dev/null
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
# A clean copy of the Lean project only (no web app, no macOS build output).
cp -R SoundAndComplete SoundAndComplete.lean Main.lean Bench.lean lakefile.toml \
  lake-manifest.json lean-toolchain comparator.json "$work/"
docker run --rm --privileged -v "$work":/proj -w /proj sac-comparator bash -c "
  mkdir -p /run/user/0
  echo '== lake check'; lake check
  echo '== lake comparator'; lake comparator $*"
