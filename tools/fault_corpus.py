#!/usr/bin/env python3
"""Evaluate the computation oracle on a fault corpus (the non-obviousness test).

oracle_check.py shows the THREE shipped cost statements survive the oracle. That
alone does not show the oracle is USEFUL -- a check that never fires catches
nothing. This harness measures the oracle's discriminating power: it feeds each
oracle unit a corpus of plausible-but-wrong closed forms ('mutants', in
tools/fault_corpus.json) and reports whether the oracle CATCHES each, against the
disposition the corpus declares it should produce:

  caught      a faithfulness bug (off-by-one, wrong constant, wrong family, ...).
              The oracle MUST reject it -- it must disagree with the enumerated
              mean at some enumerated n. A 'caught' mutant that slips through is a
              false negative and fails this harness.
  equivalent  a different syntactic form of the SAME mean. The oracle must NOT
              flag it. A flagged 'equivalent' is a false positive and fails.
  survives    an adversarial form crafted to agree on every enumerated n yet be
              wrong beyond the window. The oracle is finite consistency, not a
              proof, so it CANNOT catch this -- and that is the honest point: it
              is why the kernel proof is still required. A 'survives' mutant that
              the oracle nonetheless catches means the corpus is mis-stated.

The result is a catch rate on realistic faults (should be 100%) plus an explicit
count of the documented blind spot. Same exact-rational evaluation as
oracle_check.py (n, H(.), Fraction). Pure stdlib. Run: python3 tools/fault_corpus.py
"""
import json, pathlib, sys
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parent.parent
CORPUS = pathlib.Path(__file__).resolve().parent / "fault_corpus.json"


def H(m):  # n-th harmonic number, exact
    return sum((Fraction(1, i) for i in range(1, int(m) + 1)), Fraction(0))


def ev(expr, n):
    return eval(expr, {"__builtins__": {}}, {"n": Fraction(n), "H": H, "Fraction": Fraction})


def disagrees(p, q, ns, means):
    """True iff p/q differs from the enumerated mean at some enumerated n
    (i.e. the oracle would reject it). Also returns the first witness n."""
    for n, m in zip(ns, means):
        try:
            val = ev(p, n) / ev(q, n)
        except Exception:
            return True, n  # un-evaluable form is, conservatively, a rejection
        if val != Fraction(m):
            return True, n
    return False, None


def main() -> None:
    corpus = json.loads(CORPUS.read_text(encoding="utf-8"))
    realistic = caught = 0
    blind = bugs = 0
    print("oracle fault-corpus evaluation\n" + "=" * 60)
    for unit in corpus["units"]:
        art = ROOT / unit["artifact"]
        r = json.loads(art.read_text(encoding="utf-8"))
        ns, means = r["small_ns"], r["exact_means"]
        # sanity: the declared-correct form must itself pass the oracle
        bad, _ = disagrees(unit["correct"]["p"], unit["correct"]["q"], ns, means)
        flag = "  [!! correct form fails oracle]" if bad else ""
        if bad:
            bugs += 1
        print(f"\n{unit['id']}  (correct = ({unit['correct']['p']})/({unit['correct']['q']}), n={ns}){flag}")
        for mut in unit["mutants"]:
            rejected, witness = disagrees(mut["p"], mut["q"], ns, means)
            disp = mut["disposition"]
            if disp == "equivalent":
                ok = not rejected
                verdict = "PASS-THROUGH (correctly not flagged)" if ok else f"FALSE POSITIVE at n={witness}"
            elif disp == "survives":
                blind += 1
                ok = not rejected
                verdict = "SURVIVES (blind spot, as documented)" if ok else f"caught at n={witness} (corpus mis-stated)"
            else:  # caught
                realistic += 1
                ok = rejected
                if ok:
                    caught += 1
                verdict = f"CAUGHT at n={witness}" if ok else "FALSE NEGATIVE (slipped through!)"
            if not ok:
                bugs += 1
            mark = "ok " if ok else "ERR"
            print(f"  [{mark}] {mut['id']:<28} {mut['kind']:<14} -> {verdict}")
    print("\n" + "=" * 60)
    rate = f"{caught}/{realistic}" + (f" ({100*caught//realistic}%)" if realistic else "")
    print(f"realistic faults caught: {rate}")
    print(f"documented blind spots (survive by design): {blind}")
    if bugs:
        print(f"FAIL: {bugs} oracle/corpus discrepanc{'y' if bugs == 1 else 'ies'}")
        sys.exit(1)
    print("PASS: oracle catches every realistic fault; equivalents pass; blind spots survive as documented")


if __name__ == "__main__":
    main()
