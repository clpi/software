#!/bin/sh
set -eu
cd "$(dirname "$0")"
export PATH="${HOME}/.elan/bin:${PATH}"
if find . -name '*.lean' -not -path './.lake/*' -print0 |
  xargs -0 grep -En '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)'; then
  echo 'Prohibited proof escape hatch' >&2
  exit 1
fi
lake build -R -KwarningAsError=true
