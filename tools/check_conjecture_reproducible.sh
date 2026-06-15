#!/usr/bin/env bash
# Reproducibility lock for the conjecture track.
#
# The conjecture track is "computed, not trusted" — but the published numbers
# must at least be exactly what the committed solver deterministically produces,
# so anyone can reproduce them. This re-runs tools/conjecture/conjecture.py and
# fails if any committed tools/conjecture/results/*.json differs from the
# script's fresh output (the conjecture-track analogue of the signature-lock for
# proofs). Pure stdlib; no network, no secrets.
#
# Usage: tools/check_conjecture_reproducible.sh
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"

python3 "$root/tools/conjecture/conjecture.py" >/dev/null

if git -C "$root" diff --quiet -- tools/conjecture/results/; then
  echo "OK  tools/conjecture/results/ is reproducible from conjecture.py"
  exit 0
fi
echo "FAIL  tools/conjecture/results/ does NOT match conjecture.py output:"
git -C "$root" --no-pager diff --stat -- tools/conjecture/results/
echo
echo "Re-run the solver and commit the regenerated results:"
echo "    python3 tools/conjecture/conjecture.py"
exit 1
