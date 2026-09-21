#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export PYTHONPATH="$PWD/src"
python3 -m unittest discover -s tests -v
python3 -m tube_transport.sweep --config config/default.json --output results
