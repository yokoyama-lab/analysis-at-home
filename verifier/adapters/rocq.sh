#!/usr/bin/env bash
# Rocq (Coq) adapter.
#
# Accept iff: the submission compiles AND the named theorem is proved with NO
# axioms — i.e. `Print Assumptions <theorem>` reports "Closed under the global
# context". This is the real trustless check: it catches Admitted/admit/Axiom
# robustly, and (unlike a textual grep) does NOT false-positive on the word
# "Admitted" appearing in a comment.
#
# Args: <submission.v> <theorem-name>
# Prints a JSON verdict; exit 0 = accepted, non-zero = rejected.
set -euo pipefail

submission="${1:-}"
theorem="${2:-}"
verdict() { printf '{"accepted": %s, "reason": "%s"}\n' "$1" "$2"; }
clean() { printf '%s' "$1" | tr '\n' ' ' | sed 's/"/\\"/g' | cut -c1-240; }

[ -n "$theorem" ] || { verdict false "no theorem name given"; exit 2; }

if command -v coqc >/dev/null 2>&1; then COMPILE=(coqc -q)
elif command -v rocq >/dev/null 2>&1; then COMPILE=(rocq compile -q)
else verdict false "neither coqc nor rocq is installed"; exit 2; fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
sandbox="$(dirname "$0")/../sandbox.sh"

# Make the reusable framework library (framework/*.v) available so a submission
# may `Require Import` it (coqc resolves .vo from the compile cwd by default).
# Additive and backward-compatible: self-contained units ignore it. Each framework
# file is itself kernel-compiled here (from source, not a trusted .vo), so a unit
# that builds on it is still checked end-to-end. Best-effort: a unit that needs a
# framework module that fails to build will simply fail to compile below.
fwdir="$(cd "$(dirname "$0")/../.." && pwd)/framework"
if [ -d "$fwdir" ]; then
  for v in "$fwdir"/*.v; do
    [ -e "$v" ] || continue
    cp "$v" "$work/"
  done
  for v in "$work"/*.v; do
    [ -e "$v" ] || continue
    AAH_SANDBOX_RW="$work" bash "$sandbox" "${COMPILE[@]}" "$(basename "$v")" >/dev/null 2>&1 || true
  done
fi

cp "$submission" "$work/Submission.v"
# Ask the kernel to report what the theorem actually depends on.
printf '\nPrint Assumptions %s.\n' "$theorem" >> "$work/Submission.v"

# Run the kernel sandboxed (no network, read-only FS except $work, rlimits).
if AAH_SANDBOX_RW="$work" bash "$sandbox" "${COMPILE[@]}" Submission.v >"$work/out" 2>&1; then
  if grep -q "Closed under the global context" "$work/out"; then
    verdict true "kernel-checked: ${theorem} is closed under the global context"
  else
    verdict false "axiom check failed (Admitted/admit/Axiom?): $(clean "$(grep -iA3 'axiom' "$work/out")")"
    exit 1
  fi
else
  verdict false "coqc rejected: $(clean "$(cat "$work/out")")"
  exit 1
fi
