#!/usr/bin/env bash
# Certify the decomposed proof: concatenate the shared spec, every leaf (in
# dependency order = filename order), and the assembly, then ask the kernel
# whether the assembled theorem is axiom-free.
#
# A leaf is "done" when its file contains a real proof (no Admitted/admit). The
# theorem is CERTIFIED when this script reports "Closed under the global
# context": that means every leaf was discharged and nothing was assumed.
#
# Usage: assemble.sh            (from this directory or any cwd)
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
theorem="insertion_sort_while_comparisons_upper_bound"

if command -v coqc >/dev/null 2>&1; then COMPILE=(coqc -q)
elif command -v rocq >/dev/null 2>&1; then COMPILE=(rocq compile -q)
else echo "neither coqc nor rocq is installed" >&2; exit 2; fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
full="$work/Assembled.v"

# spec, then leaves in lexical (= dependency) order, then the assembly.
cat "$here/spec.v" > "$full"
n=0
for leaf in "$here"/leaves/*.v; do
  cat "$leaf" >> "$full"
  n=$((n + 1))
done
cat "$here/main.v" >> "$full"
printf '\nPrint Assumptions %s.\n' "$theorem" >> "$full"

echo "Assembled spec + ${n} leaves + main."
if ( cd "$work" && "${COMPILE[@]}" Assembled.v ) >"$work/out" 2>&1; then
  if grep -q "Closed under the global context" "$work/out"; then
    echo "CERTIFIED: ${theorem} is closed under the global context (no axioms; all ${n} leaves discharged)."
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
