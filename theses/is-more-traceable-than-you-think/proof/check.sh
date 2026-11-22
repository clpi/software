#!/bin/sh
# Check every repository Lean source against the original two-axiom budget.
set -eu
cd "$(dirname "$0")/.."
exec python3 proof/audit.py
