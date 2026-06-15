#!/usr/bin/env bash
# Signature-equivalence guard for analysis@home submissions.
#
# A kernel "accepted" verdict proves that a theorem of the right NAME holds with
# no axioms — but not that it is the SAME statement the unit intends. A PR could
# weaken the theorem (or change a fixed cost-model definition) while keeping the
# name. This guard locks the statement: when a proof target already exists on the
# base branch, the submission must prove the IDENTICAL statement of the named
# theorem; only the proof may change.
#
# Usage: signature_lock.sh <backend> <theorem> <base-file> <submission-file>
#   exit 0  statements match, OR could not be decided (kernel + review still gate)
#   exit 1  the statement was CHANGED (rejected)
#
# Heuristic + conservative: the statement is the text from the theorem keyword
# (or, for Agda, the type signature) up to the proof delimiter, with whitespace
# normalised. If extraction yields nothing on either side we WARN and pass —
# this layer never blocks a legitimate proof-only change; the kernel check and
# human review remain the primary gates. Limitation: a comment containing a
# proof keyword between the statement and its proof could cut early.
set -uo pipefail

backend="${1:-}"; thm="${2:-}"; base="${3:-}"; sub="${4:-}"

# Extract the named theorem's statement, normalised to one space-separated line.
stmt() { # <file>
  local f="$1" txt
  txt="$(tr '\n\t' '  ' < "$f" | tr -s ' ')"
  case "$backend" in
    rocq)
      printf '%s' "$txt" | grep -oP \
        "(Theorem|Lemma|Corollary|Proposition|Example|Fact|Remark|Definition)\s+${thm}\b.*?(?=\s(Proof|Qed|Defined|Admitted)\b|:=)" | head -1 ;;
    lean)
      printf '%s' "$txt" | grep -oP \
        "(theorem|lemma|def|example)\s+${thm}\b.*?(?=:=)" | head -1 ;;
    isabelle)
      printf '%s' "$txt" | grep -oP \
        "(lemma|theorem|corollary|proposition)\s+${thm}\b.*?(?=\s(proof|by|apply|using|unfolding|sorry|oops|done)\b)" | head -1 ;;
    agda)
      printf '%s' "$txt" | grep -oP \
        "(^|\s)${thm}\s*:.*?(?=\s${thm}\s*=)" | head -1 ;;
    *) return 0 ;;
  esac
}

[ -f "$base" ] || { echo "NOTE  no base version — statement established by this PR (kernel-checked; review the statement)"; exit 0; }

sb="$(stmt "$base")"; ss="$(stmt "$sub")"
sb="$(printf '%s' "$sb" | sed 's/^ *//; s/ *$//')"
ss="$(printf '%s' "$ss" | sed 's/^ *//; s/ *$//')"

if [ -z "$sb" ] || [ -z "$ss" ]; then
  echo "WARN  could not extract the statement of '${thm}' (${backend}) — relying on kernel + review"
  exit 0
fi
if [ "$sb" = "$ss" ]; then
  echo "LOCK  statement of '${thm}' is unchanged from base (signature-equivalent)"
  exit 0
fi
echo "FAIL  statement of '${thm}' CHANGED vs base — submission is not signature-equivalent"
echo "  base: ${sb}"
echo "  sub : ${ss}"
exit 1
