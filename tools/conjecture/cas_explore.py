#!/usr/bin/env python3
"""analysis@home — conjecture track, computer-algebra (sympy) exploration.

OPTIONAL and NOT run in CI. The pure-stdlib engine (conjecture.py) covers the
distributions and the polynomial / poly·r^k closed-form sums with no third-party
dependency. This script reaches for a full CAS where it genuinely helps:

  - recurrences with variable coefficients (quicksort average), which the
    stdlib finite-difference / antidifference machinery does not solve;
  - cross-checking the Gosper antidifference of the weighted geometric sum.

Everything here is still a CONJECTURE: sympy's output is not trusted. The point
is to emit a closed form AND a checkable certificate (an identity a proof
assistant can confirm by routine induction) for the verify track.

Run:  python3 -m venv .venv && .venv/bin/pip install sympy
      .venv/bin/python tools/conjecture/cas_explore.py
"""
from __future__ import annotations
import json, pathlib

HERE = pathlib.Path(__file__).resolve().parent
RESULTS = HERE / "results"

try:
    import sympy as sp
except ModuleNotFoundError:
    raise SystemExit(
        "sympy not installed — this CAS exploration is optional.\n"
        "  python3 -m venv .venv && .venv/bin/pip install sympy\n"
        "  .venv/bin/python tools/conjecture/cas_explore.py\n"
        "(the pure-stdlib conjecture.py needs no dependencies and is what CI runs)."
    )


def quicksort_average() -> dict:
    """Average key comparisons of randomized quicksort.

    Full-history recurrence:  C(n) = (n-1) + (2/n) Σ_{k=0}^{n-1} C(k),  C(0)=0.
    Reduce to a first-order recurrence by subtracting nC(n) and (n-1)C(n-1):
        n·C(n) = (n+1)·C(n-1) + 2(n-1).
    Conjectured closed form:  C(n) = 2(n+1)H_n − 4n.
    We VERIFY the closed form satisfies the reduced recurrence exactly (the
    certificate a proof assistant would re-check), since sympy's rsolve does not
    crack this variable-coefficient recurrence directly.
    """
    n = sp.symbols("n", integer=True, positive=True)
    Hn, Hn1 = sp.symbols("H_n H_{n-1}")  # H_n and H_{n-1}
    C = lambda Hm, m: 2 * (m + 1) * Hm - 4 * m
    # residual of n·C(n) − (n+1)·C(n-1) − 2(n-1), with H_n = H_{n-1} + 1/n
    residual = (n * C(Hn, n) - ((n + 1) * C(Hn1, n - 1) + 2 * (n - 1))).subs(
        Hn, Hn1 + sp.Rational(1, 1) / n
    )
    residual = sp.simplify(residual)
    H = sp.harmonic
    small = {int(m): str(sp.nsimplify(2 * (m + 1) * H(m) - 4 * m)) for m in range(0, 7)}
    return {
        "kind": "recurrence",
        "algorithm": "quicksort average comparisons (random pivot)",
        "summand": "C(n) = (n−1) + (2/n)·Σ_{k<n} C(k),  C(0)=0",
        "conjectured_mean_closed_form": "2·(n+1)·H_n − 4·n   (H_n = Σ_{i=1}^n 1/i)",
        "certificate": "reduced recurrence  n·C(n) = (n+1)·C(n−1) + 2(n−1); "
                       f"residual after substituting the closed form = {residual}",
        "certificate_verified": residual == 0,
        "small_values": small,
        "limit_distribution": None,
        "histogram_at_limit_n": "",
        "note": "CAS-verified conjecture, now also kernel-checked: the verify-track "
                "twin work-units/quicksort-average-comparisons proves C n == Cf n in "
                "QArith (rationals + harmonic numbers), axiom-free.",
    }


def weighted_geometric_cross_check() -> dict:
    """Cross-check the stdlib antidifference of Σ k·2^k against sympy/Gosper."""
    from sympy.concrete.gosper import gosper_sum
    k, n = sp.symbols("k n", integer=True, nonnegative=True)
    closed = sp.simplify(sp.summation(k * 2 ** k, (k, 0, n - 1)))
    g = gosper_sum(k * 2 ** k, k)  # antidifference g with g(k+1)-g(k)=k·2^k
    return {
        "kind": "cross-check",
        "algorithm": "Σ k·2^k  (sympy/Gosper cross-check of the stdlib solver)",
        "sympy_closed_form": str(closed),
        "gosper_antidifference": str(g),
        "agrees_with_stdlib": str(sp.expand(closed)) == str(sp.expand((n - 2) * 2 ** n + 2)),
    }


def main() -> None:
    RESULTS.mkdir(parents=True, exist_ok=True)
    qs = quicksort_average()
    (RESULTS / "quicksort-average.json").write_text(
        json.dumps(qs, ensure_ascii=False, indent=2), encoding="utf-8")
    print("# quicksort average comparisons")
    print(f"  C(n) = {qs['conjectured_mean_closed_form']}")
    print(f"  {qs['certificate']}  [verified={qs['certificate_verified']}]")
    print(f"  small: {qs['small_values']}")
    print()
    cc = weighted_geometric_cross_check()
    print("# Σ k·2^k — sympy/Gosper cross-check")
    print(f"  sympy closed form : {cc['sympy_closed_form']}")
    print(f"  Gosper antidiff   : {cc['gosper_antidifference']}")
    print(f"  agrees with stdlib (n−2)·2^n+2 : {cc['agrees_with_stdlib']}")


if __name__ == "__main__":
    main()
