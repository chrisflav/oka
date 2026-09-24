#!/usr/bin/env bash
# Run before starting work on the `oka` repository.
#
# Fetches the prebuilt Mathlib artifacts. Without this the first `lake build` compiles
# Mathlib from source, which takes hours; with it, a full build of this project is a
# couple of minutes.

set -uo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1

lake exe cache get
