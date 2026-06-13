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
cp "$submission" "$work/Submission.v"
# Ask the kernel to report what the theorem actually depends on.
printf '\nPrint Assumptions %s.\n' "$theorem" >> "$work/Submission.v"

# TODO (sandbox): run this inside an isolated container before accepting
# submissions from the public internet (see verifier/README.md).
if ( cd "$work" && "${COMPILE[@]}" Submission.v ) >"$work/out" 2>&1; then
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
