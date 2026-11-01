#!/usr/bin/env bash
# Run `lake check` and `lake comparator` in a Linux container (they need the
# Linux `bwrap` sandbox, so they cannot run directly on macOS).
# Usage: comparator/run.sh [--paranoid]
set -euo pipefail
cd "$(dirname "$0")/.."
docker build -q -t sac-comparator comparator >/dev/null
# Inside the project, not the system temp folder: Colima shares only the home
# folder with its VM, so a mount from /var/folders would look empty.
mkdir -p .lake
work=$(mktemp -d "$PWD/.lake/comparator.XXXXXX")
trap 'rm -rf "$work"' EXIT
# A clean copy of the Lean project only (no web app, no macOS build output).
cp -R SoundAndComplete SoundAndComplete.lean Main.lean Bench.lean lakefile.toml \
  lake-manifest.json lean-toolchain comparator.json "$work/"
docker run --rm --privileged -v "$work":/proj -w /proj sac-comparator bash -c "
  set -e  # so a failed lake check fails this script too
  mkdir -p /run/user/0
  echo '== lake check'; lake check
  echo '== lake comparator'; lake comparator $*"
