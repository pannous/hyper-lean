#!/bin/bash
# Build and check Hyper/HyperBasics.lean (the generic hyperreal identities,
# proved once against the IsHyperReal interface and valid for every backend).

set -e

cd "$(dirname "$0")"
lake build Hyper.HyperBasics
