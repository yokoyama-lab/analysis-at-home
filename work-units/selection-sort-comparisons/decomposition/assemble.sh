#!/usr/bin/env bash
# Certify a decomposed proof: concatenate spec + leaves (filename order =
# dependency order) + main, then ask the kernel whether the theorem named in
# leaves.json is axiom-free ("Closed under the global context"). Generic: reads
# the theorem name from leaves.json so the same script works for every unit.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
theorem="$(grep -o '"theorem"[[:space:]]*:[[:space:]]*"[^"]*"' "$here/leaves.json" \
            | head -1 | sed 's/.*: *"//; s/".*//')"
[ -n "$theorem" ] || { echo "no theorem in leaves.json" >&2; exit 2; }

if command -v coqc >/dev/null 2>&1; then COMPILE=(coqc -q)
elif command -v rocq >/dev/null 2>&1; then COMPILE=(rocq compile -q)
else echo "neither coqc nor rocq is installed" >&2; exit 2; fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
full="$work/Assembled.v"
cat "$here/spec.v" > "$full"
n=0
for leaf in "$here"/leaves/*.v; do cat "$leaf" >> "$full"; n=$((n + 1)); done
cat "$here/main.v" >> "$full"
printf '\nPrint Assumptions %s.\n' "$theorem" >> "$full"

echo "Assembled spec + ${n} leaves + main."
if ( cd "$work" && "${COMPILE[@]}" Assembled.v ) >"$work/out" 2>&1; then
  if grep -q "Closed under the global context" "$work/out"; then
    echo "CERTIFIED: ${theorem} is closed under the global context (all ${n} leaves discharged)."
    exit 0
  fi
  echo "NOT certified — the theorem still depends on assumptions:" >&2
  grep -iA20 'axiom' "$work/out" >&2 || true
  exit 1
else
  echo "Assembly failed to compile:" >&2
  tail -n 20 "$work/out" >&2
  exit 1
fi
