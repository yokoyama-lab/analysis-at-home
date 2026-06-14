#!/usr/bin/env bash
# Agda adapter.
#
# Accept iff `agda --safe` type-checks the submission (which rejects unsafe
# features and any unsolved holes `?`/`{!!}`) AND the file declares no
# `postulate` (Agda's axiom escape hatch). agda-stdlib is made available via a
# generated scratch.agda-lib. The temp file is named after the submission's
# top-level module so Agda's filename = module-name rule holds.
#
# Limitation (Phase 1): the postulate check is textual (a comment mentioning
# "postulate" would false-positive — keep them out of submissions).
#
# Args: <submission.agda> <theorem-name>
set -euo pipefail
submission="${1:-}"
theorem="${2:-}"
verdict() { printf '{"accepted": %s, "reason": "%s"}\n' "$1" "$2"; }
clean() { printf '%s' "$1" | tr '\n' ' ' | sed 's/"/\\"/g' | cut -c1-240; }

command -v agda >/dev/null 2>&1 || { verdict false "agda not installed"; exit 2; }
[ -n "$theorem" ] || { verdict false "no theorem name given"; exit 2; }

if grep -Eq '^[[:space:]]*postulate\b' "$submission"; then
  verdict false "submission declares a postulate (axiom)"; exit 1
fi
grep -q "$theorem" "$submission" || { verdict false "theorem ${theorem} not found"; exit 1; }

mod="$(grep -m1 -oE '^module[[:space:]]+[A-Za-z0-9_.]+' "$submission" | awk '{print $2}')"
[ -n "$mod" ] || { verdict false "no top-level module declaration"; exit 1; }
file="${mod##*.}.agda"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cp "$submission" "$work/$file"
cat > "$work/scratch.agda-lib" <<LIB
name: scratch
include: .
depend: standard-library
LIB

sandbox="$(dirname "$0")/../sandbox.sh"
if AAH_SANDBOX_RW="$work" bash "$sandbox" agda --safe "$file" >"$work/out" 2>&1; then
  verdict true "agda --safe type-checked ${theorem}; no postulate"
else
  verdict false "agda rejected: $(clean "$(cat "$work/out")")"
  exit 1
fi
