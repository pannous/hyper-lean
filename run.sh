#!/bin/bash
# Build and check Hyper/HyperBasics.lean (the generic hyperreal identities,
# proved once against the IsHyperReal interface and valid for every backend).

set -e

cd ~/dev/script/lean4/hyper/

cd "$(dirname "$0")"
echo HyperReal definitions and lemmas via Hyper.HyperBasics
lake build Hyper.HyperBasics
echo some examples in hyper.lean
lake env lean hyper.lean
