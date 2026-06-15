#!/usr/bin/env python3
"""Oracle faithfulness check (the compute -> test-the-spec -> prove method).

A kernel "accepted" verdict only says a theorem of the right NAME holds; it does
not say the cost STATEMENT is the intended one. For average-case units we have an
independent ground truth: the conjecture track (tools/conjecture/) computes
E[cost(n)] by exhaustive ENUMERATION. This check makes a unit's formal mean face
that oracle: a unit may declare

    "oracle": {"p": "<expr in n>", "q": "<expr in n>",
               "artifact": "tools/conjecture/results/<file>.json"}

meaning its theorem proves E[cost] = p/q. We evaluate p/q (exactly, over the
rationals) at every small n the artifact enumerated and require it to equal the
enumerated mean. A weakened or mis-translated closed form is caught here, before
(and independently of) the kernel proof.

Pure stdlib. Run: python3 tools/oracle_check.py
"""
import json, pathlib, sys
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parent.parent
WU = ROOT / "work-units"


def H(m):  # n-th harmonic number, exact
    return sum((Fraction(1, i) for i in range(1, int(m) + 1)), Fraction(0))


def ev(expr, n):
    # exprs are author-written, restricted to n, H(.) and rational arithmetic
    return eval(expr, {"__builtins__": {}}, {"n": Fraction(n), "H": H, "Fraction": Fraction})


def main() -> None:
    checked = fail = 0
    for uj in sorted(WU.glob("*/unit.json")):
        unit = json.loads(uj.read_text(encoding="utf-8"))
        orc = unit.get("oracle")
        if not orc:
            continue
        art = ROOT / orc["artifact"]
        if not art.exists():
            print(f"FAIL {unit['id']}: oracle artifact {orc['artifact']} missing"); fail += 1; continue
        r = json.loads(art.read_text(encoding="utf-8"))
        ns, means = r.get("small_ns"), r.get("exact_means")
        if not ns or not means:
            print(f"SKIP {unit['id']}: artifact has no small_ns / exact_means"); continue
        ok = True
        for n, m in zip(ns, means):
            try:
                formal = ev(orc["p"], n) / ev(orc["q"], n)
            except Exception as e:
                print(f"FAIL {unit['id']}: cannot evaluate p/q at n={n}: {e}"); ok = False; break
            if formal != Fraction(m):
                print(f"FAIL {unit['id']}: n={n}  formal ({orc['p']})/({orc['q']})={formal}"
                      f"  !=  enumerated {m}"); ok = False
        checked += 1
        if ok:
            print(f"PASS {unit['id']}: formal mean = enumerated E[cost] over n={ns}")
        else:
            fail += 1
    print(f"oracle-check: {checked} unit(s) checked, {fail} failure(s)")
    sys.exit(1 if fail else 0)


if __name__ == "__main__":
    main()
