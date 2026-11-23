#!/bin/sh
# Gate for the shared core library and every bridge to a thesis's own definitions.
set -eu
cd "$(dirname "$0")"
exec python3 check_bridges.py
