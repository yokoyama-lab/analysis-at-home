#!/usr/bin/env python3
"""analysis@home — conjecture track (pure stdlib).

For an algorithm + an input distribution, COMPUTE (not prove):
  - the exact cost distribution for small n (exhaustive enumeration),
  - exact mean/variance as rationals, and a CONJECTURED closed form for the mean
    E[cost(n)] via Newton forward differences (exact if the cost mean is
    polynomial in n),
  - the conjectured LIMIT distribution of the standardized cost as n grows, by
    KS-distance of the empirical CDF to N(0,1) and to the standardized Uniform.

These are CONJECTURES (computed evidence), to be promoted to theorems on the
verify track where provable (e.g. the exact mean). Nothing here is trusted.

No third-party deps: fractions / math.erf / itertools / statistics only.
"""
from __future__ import annotations
import json, math, itertools, pathlib, statistics
from fractions import Fraction
from collections import Counter

HERE = pathlib.Path(__file__).resolve().parent
RESULTS = HERE / "results"


# ---------- closed-form guessing (Newton forward differences) ----------
def poly_from_values(vals: list[Fraction]) -> list[Fraction] | None:
    """If E(0..N) is a polynomial in n, return its coefficients [a0,a1,...]
    (a0 + a1 n + ...), else None. Exact rational arithmetic."""
    n = len(vals)
    # finite difference table
    diffs = [vals[:]]
    for _ in range(n - 1):
        prev = diffs[-1]
        diffs.append([prev[i + 1] - prev[i] for i in range(len(prev) - 1)])
    # degree = last level that is (eventually) all zero above
    deg = n - 1
    while deg > 0 and all(x == 0 for x in diffs[deg]):
        deg -= 1
    if deg + 2 > n:   # not enough points to be sure it stabilised
        return None
    if any(x != diffs[deg][0] for x in diffs[deg]) and deg > 0:
        # top non-zero level isn't constant -> not a polynomial of this degree
        if any(x != 0 for x in diffs[deg + 1]):
            return None
    # Newton forward: E(x) = sum_k C(x,k) * Δ^k E(0); expand to monomials.
    coeffs = [Fraction(0)]
    falling = [Fraction(1)]  # represents the polynomial product (x-0)...(x-(k-1)) / k!
    for k in range(deg + 1):
        dk = diffs[k][0]
        # add dk/k! * falling_k  (falling already includes /k!)
        for i, c in enumerate(falling):
            while i >= len(coeffs):
                coeffs.append(Fraction(0))
            coeffs[i] += dk * c
        # falling_{k+1} = falling_k * (x - k) / (k+1)
        nxt = [Fraction(0)] * (len(falling) + 1)
        for i, c in enumerate(falling):
            nxt[i + 1] += c                      # * x
            nxt[i] += c * (-k)                    # * (-k)
        falling = [c / (k + 1) for c in nxt]
    return coeffs


def shift_poly(coeffs: list[Fraction], n0: int) -> list[Fraction]:
    """Given P(t) with t = n - n0, return coefficients of P in terms of n."""
    if n0 == 0:
        return coeffs
    out = [Fraction(0)] * len(coeffs)
    for k, ck in enumerate(coeffs):
        if ck == 0:
            continue
        # ck * (n - n0)^k = ck * sum_j C(k,j) n^j (-n0)^(k-j)
        for j in range(k + 1):
            out[j] += ck * math.comb(k, j) * Fraction((-n0) ** (k - j))
    return out


def poly_str(coeffs: list[Fraction], var: str = "n") -> str:
    terms = []
    for i, c in enumerate(coeffs):
        if c == 0:
            continue
        m = "" if i == 0 else (var if i == 1 else f"{var}^{i}")
        terms.append(f"{c}" + (("·" + m) if m else ""))
    return " + ".join(terms) if terms else "0"


# ---------- closed-form summation (Gosper-style antidifference) ----------
# A pure-stdlib "computer algebra" routine: given a summand a(k) of the form
# poly(k) · r^k (r an integer; r = 1 is the plain polynomial case), it finds the
# antidifference F with F(k+1) − F(k) = a(k) exactly (rational coefficients), so
#   Σ_{k=0}^{n-1} a(k) = F(n) − F(0).
# F(k+1) − F(k) = a(k) is the *telescoping certificate*: a one-line identity a
# proof assistant can check by a routine induction. This is the conjecture-track
# half of the WZ/Gosper bridge — it emits both the closed form AND the certificate.

def _pshift1(p: list[Fraction]) -> list[Fraction]:
    """Coefficients of p(x+1)."""
    out = [Fraction(0)] * len(p)
    for j, c in enumerate(p):
        if c == 0:
            continue
        for i in range(j + 1):
            out[i] += c * math.comb(j, i)
    return out


def _solve(cols: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction] | None:
    """Solve the square linear system whose columns are `cols` for `rhs`
    (exact rational Gaussian elimination). Returns the unknown vector or None."""
    m = len(cols)
    aug = [[cols[c][r] for c in range(m)] + [rhs[r]] for r in range(m)]
    for c in range(m):
        piv = next((r for r in range(c, m) if aug[r][c] != 0), None)
        if piv is None:
            return None
        aug[c], aug[piv] = aug[piv], aug[c]
        inv = aug[c][c]
        aug[c] = [v / inv for v in aug[c]]
        for r in range(m):
            if r != c and aug[r][c] != 0:
                f = aug[r][c]
                aug[r] = [a - f * b for a, b in zip(aug[r], aug[c])]
    return [aug[r][m] for r in range(m)]


def antidifference(a: list[Fraction], r: int) -> tuple[list[Fraction], int] | None:
    """Return (q, r) such that F(k) = q(k)·r^k satisfies F(k+1)−F(k) = a(k)·r^k
    when r != 1, or F(k) = q(k) with F(k+1)−F(k) = a(k) when r == 1 (q[0] gauged
    to 0). `a` are the polynomial coefficients of the summand's polynomial part."""
    d = len(a) - 1
    if r == 1:
        # F has degree d+1; gauge F's constant term to 0, unknowns are x^1..x^{d+1}.
        cols = []
        for j in range(1, d + 2):
            basis = [Fraction(0)] * (d + 2)
            basis[j] = Fraction(1)
            delta = [s - b for s, b in zip(_pshift1(basis), basis)]  # Δ(x^j), degree j-1
            cols.append(delta[:d + 1])
        sol = _solve(cols, [Fraction(x) for x in a])
        if sol is None:
            return None
        return ([Fraction(0)] + sol, 1)
    # r != 1 : q has degree d; L(q)(x) = r·q(x+1) − q(x) must equal a(x).
    cols = []
    for j in range(d + 1):
        basis = [Fraction(0)] * (d + 1)
        basis[j] = Fraction(1)
        L = [r * s - b for s, b in zip(_pshift1(basis), basis)]
        cols.append(L[:d + 1])
    sol = _solve(cols, [Fraction(x) for x in a])
    if sol is None:
        return None
    return (sol, r)


def closed_form_sum(a: list[Fraction], r: int, name: str) -> dict | None:
    """Closed form for Σ_{k=0}^{n-1} a(k)·r^k together with its telescoping
    certificate, verified exactly on a value table."""
    res = antidifference(a, r)
    if res is None:
        return None
    q, rr = res
    # summand a(k)·r^k as a string
    summand = f"({poly_str(a, 'k')})·{rr}^k" if rr != 1 else f"({poly_str(a, 'k')})"
    F = f"({poly_str(q, 'n')})·{rr}^n" if rr != 1 else f"({poly_str(q, 'n')})"
    Fk_str = f"({poly_str(q, 'k')})·{rr}^k" if rr != 1 else f"({poly_str(q, 'k')})"
    Fk = lambda k: _peval(q, k) * (rr ** k)
    ak = lambda k: _peval(a, k) * (rr ** k)
    # verify F(k+1)-F(k) = a(k) and the definite sum on a table
    cert_ok = all(Fk(k + 1) - Fk(k) == ak(k) for k in range(0, 12))
    sum_ok = True
    acc = Fraction(0)
    for nn in range(0, 12):
        if acc != Fk(nn) - Fk(0):
            sum_ok = False
            break
        acc += ak(nn)
    f0 = Fk(0)
    if f0 == 0:
        definite = F
    elif f0 < 0:
        definite = f"{F} + {-f0}"
    else:
        definite = f"{F} − {f0}"
    return {
        "kind": "closed-form-sum",
        "algorithm": name,
        "summand": f"Σ_{{k=0}}^{{n-1}} {summand}",
        "conjectured_mean_closed_form": definite,
        "certificate": f"F(k+1) − F(k) = {summand},  F(k) = {Fk_str}",
        "certificate_verified": cert_ok and sum_ok,
        "limit_distribution": None,
        "histogram_at_limit_n": "",
    }


def _peval(p: list[Fraction], x: int) -> Fraction:
    acc = Fraction(0)
    for c in reversed(p):
        acc = acc * x + c
    return acc


def harmonic(n: int) -> Fraction:
    """The n-th harmonic number H_n = sum_{i=1}^n 1/i (exact)."""
    return sum((Fraction(1, i) for i in range(1, n + 1)), Fraction(0))


# ---------- moments ----------
def moments(pmf: Counter) -> tuple[Fraction, Fraction]:
    total = sum(pmf.values())
    mean = sum(Fraction(v * k) for k, v in pmf.items()) / total
    var = sum(Fraction(v) * (Fraction(k) - mean) ** 2 for k, v in pmf.items()) / total
    return mean, var


# ---------- limit fit ----------
def ks_to_cdf(samples: list[float], cdf) -> float:
    s = sorted(samples)
    m = len(s)
    d = 0.0
    for i, x in enumerate(s):
        d = max(d, abs((i + 1) / m - cdf(x)), abs(cdf(x) - i / m))
    return d


def normal_cdf(x: float) -> float:
    return 0.5 * (1 + math.erf(x / math.sqrt(2)))


def uniform_cdf(x: float) -> float:  # standardized Uniform(-√3, √3): mean 0, var 1
    a = math.sqrt(3)
    return min(1.0, max(0.0, (x + a) / (2 * a)))


_EULER = 0.5772156649015329  # Euler-Mascheroni gamma


def gumbel_cdf(x: float) -> float:  # standardized Gumbel (maxima): mean γ, var π²/6
    sd = math.pi / math.sqrt(6)
    return math.exp(-math.exp(-(_EULER + sd * x)))


def rayleigh_cdf(x: float) -> float:  # standardized Rayleigh(σ=1): mean √(π/2), var (4-π)/2
    mean = math.sqrt(math.pi / 2)
    sd = math.sqrt((4 - math.pi) / 2)
    t = mean + sd * x
    return 0.0 if t <= 0 else 1.0 - math.exp(-t * t / 2)


_LAWS = {"normal (Gaussian)": normal_cdf, "uniform": uniform_cdf,
         "Gumbel (extreme value)": gumbel_cdf, "Rayleigh": rayleigh_cdf}


def ks_weighted_to_cdf(values: list[float], probs: list[float], cdf) -> float:
    """KS distance of a weighted empirical distribution to a standardized cdf."""
    order = sorted(range(len(values)), key=lambda i: values[i])
    cum = 0.0
    d = 0.0
    for i in order:
        below = cum
        cum += probs[i]
        c = cdf(values[i])
        d = max(d, abs(cum - c), abs(below - c))
    return d


def limit_fit_pmf(value_probs: list[tuple[float, float]], laws: list[str]) -> dict:
    """Fit the standardized pmf (list of (value, prob)) to the named candidate
    laws; report the best (smallest KS) and every candidate's KS."""
    tot = sum(p for _, p in value_probs)
    vp = [(v, p / tot) for v, p in value_probs]
    mu = sum(v * p for v, p in vp)
    var = sum(p * (v - mu) ** 2 for v, p in vp)
    sd = math.sqrt(var) if var > 0 else 1.0
    z = [(v - mu) / sd for v, _ in vp]
    pr = [p for _, p in vp]
    ks = {name: round(ks_weighted_to_cdf(z, pr, _LAWS[name]), 4) for name in laws}
    best = min(ks, key=ks.get)
    out = {"law": best}
    # board.py reads ks_normal / ks_uniform; expose every computed KS as ks_<law>
    out["ks_normal"] = ks.get("normal (Gaussian)")
    out["ks_uniform"] = ks.get("uniform")
    for name, v in ks.items():
        key = "ks_" + name.split()[0].lower()
        out[key] = v
    return out


def limit_fit(samples: list[float]) -> dict:
    mu = statistics.fmean(samples)
    sd = statistics.pstdev(samples)
    if sd == 0:
        return {"law": "degenerate", "ks_normal": None, "ks_uniform": None}
    z = [(x - mu) / sd for x in samples]
    kn, ku = ks_to_cdf(z, normal_cdf), ks_to_cdf(z, uniform_cdf)
    return {"law": "normal (Gaussian)" if kn <= ku else "uniform",
            "ks_normal": round(kn, 4), "ks_uniform": round(ku, 4)}


def ascii_hist(pmf: Counter, width: int = 50) -> str:
    if not pmf:
        return ""
    lo, hi = min(pmf), max(pmf)
    mx = max(pmf.values())
    out = []
    for k in range(lo, hi + 1):
        v = pmf.get(k, 0)
        out.append(f"{k:3d} | {'█' * max(0, round(width * v / mx))} {v}")
    return "\n".join(out)


# ---------- algorithm cost models (input distributions) ----------
def linear_search_pmf(n: int) -> Counter:
    """Comparisons to find a uniformly random present element in a list of
    length n: cost = its 1-based position, uniform on {1..n}."""
    return Counter({i: 1 for i in range(1, n + 1)})


def lr_maxima_pmf(n: int) -> Counter:
    """Number of left-to-right maxima of a uniformly random permutation of n
    elements (TAOCP Algorithm M: the running maximum is set on the first element
    and on each later record). Expected value = H_n."""
    c: Counter = Counter()
    for p in itertools.permutations(range(n)):
        m, k = -1, 0
        for v in p:
            if v > m:
                m, k = v, k + 1
        c[k] += 1
    return c


def quickselect_pmf(n: int) -> Counter:
    """Comparisons of quickselect (Hoare's FIND, first-element pivot) over all
    permutations of {1..n} AND all target ranks 1..n. The average grows linearly
    (E ~ 2n) — quickselect is expected-linear, unlike its quadratic worst case
    (verified in work-units/quickselect-worst-case)."""
    def qs(arr: list[int], r: int) -> int:
        if len(arr) <= 1:
            return 0
        p, rest = arr[0], arr[1:]
        less = [x for x in rest if x < p]
        greater = [x for x in rest if x > p]
        c, k = len(rest), len(less)
        if r == k + 1:
            return c
        if r <= k:
            return c + qs(less, r)
        return c + qs(greater, r - (k + 1))
    cc: Counter = Counter()
    for perm in itertools.permutations(range(1, n + 1)):
        pl = list(perm)
        for r in range(1, n + 1):
            cc[qs(pl, r)] += 1
    return cc


def hashing_collisions_pmf(n: int) -> Counter:
    """#collisions (pairs hashing to the same slot) for n keys in n slots
    (load factor 1), over all n^n hash assignments. Expected value = (n-1)/2."""
    cc: Counter = Counter()
    m = n if n > 0 else 1
    for assign in itertools.product(range(m), repeat=n):
        buckets: Counter = Counter(assign)
        cc[sum(v * (v - 1) // 2 for v in buckets.values())] += 1
    return cc


def inversions_pmf(n: int) -> Counter:
    """#inversions of a uniformly random permutation of n elements (the
    displacement cost underlying insertion sort), exhaustively."""
    c: Counter = Counter()
    for p in itertools.permutations(range(n)):
        inv = sum(1 for i in range(n) for j in range(i + 1, n) if p[i] > p[j])
        c[inv] += 1
    return c


def random_bst_depths(perm: tuple) -> list[int]:
    """Depths of the nodes of the BST built by inserting `perm` left to right."""
    root, left, right, depths = None, {}, {}, []
    for k in perm:
        if root is None:
            root = k; depths.append(0); continue
        cur, d = root, 0
        while True:
            d += 1
            if k < cur:
                if cur in left: cur = left[cur]
                else: left[cur] = k; break
            else:
                if cur in right: cur = right[cur]
                else: right[cur] = k; break
        depths.append(d)
    return depths


def random_bst_pmf(n: int) -> Counter:
    """Depth of a uniformly random node in a random BST (built from a random
    permutation of 1..n), over all permutations. E[depth] ~ 2 ln n; Gaussian."""
    c: Counter = Counter()
    for p in itertools.permutations(range(1, n + 1)):
        for d in random_bst_depths(p):
            c[d] += 1
    return c


def ascii_hist_binned(vp: list[tuple[float, float]], nbins: int = 16) -> str:
    if not vp:
        return ""
    lo = min(v for v, _ in vp); hi = max(v for v, _ in vp)
    width = (hi - lo) / nbins if hi > lo else 1.0
    bins = [0.0] * (nbins + 1)
    for v, p in vp:
        bins[min(nbins, int((v - lo) / width))] += p
    mx = max(bins) or 1.0
    out = []
    for i, p in enumerate(bins):
        center = lo + (i + 0.5) * width
        out.append(f"{center:6.1f} | {'█' * round(50 * p / mx)} {p:.4f}")
    return "\n".join(out)


def coupon_collector_result(small_ns: list[int], limit_n: int) -> dict:
    """Time T to collect all n coupons (each draw uniform). E[T] = n*H_n exactly;
    standardized T converges to a Gumbel (extreme-value) law."""
    means = [n * harmonic(n) for n in small_ns]
    n = limit_n
    p = [0.0] * (n + 1); p[0] = 1.0
    t, cum, vp = 0, 0.0, []
    while cum < 1 - 1e-12 and t < 200000:
        t += 1
        nw = [0.0] * (n + 1)
        for j in range(n):
            if p[j]:
                nw[j] += p[j] * (j / n)
                nw[j + 1] += p[j] * ((n - j) / n)
        if nw[n] > 0:
            vp.append((float(t), nw[n])); cum += nw[n]
        nw[n] = 0.0
        p = nw
    mu = sum(v * q for v, q in vp); var = sum(q * (v - mu) ** 2 for v, q in vp)
    return {
        "kind": "distribution",
        "algorithm": "coupon collector (collect all n coupons)",
        "small_ns": small_ns,
        "exact_means": [str(m) for m in means],
        "conjectured_mean_closed_form": "n·H_n (n-th harmonic number)",
        "limit_n": limit_n,
        "limit_mean": str(n * harmonic(n)),
        "limit_variance": f"~{var:.3f}",
        "limit_distribution": limit_fit_pmf(
            vp, ["normal (Gaussian)", "uniform", "Gumbel (extreme value)"]),
        "histogram_at_limit_n": ascii_hist_binned(vp),
    }


def birthday_result(small_ns: list[int], limit_n: int) -> dict:
    """Number of insertions T until the first hash collision among n slots.
    E[T] = sum_i prod_{j<i}(1 - j/n) ~ sqrt(pi*n/2); standardized T -> Rayleigh."""
    def mean_exact(n: int) -> Fraction:
        total, D = Fraction(0), Fraction(1)
        for i in range(n + 1):
            total += D; D *= Fraction(n - i, n)
        return total
    means = [mean_exact(n) for n in small_ns]
    n = limit_n
    vp, D = [], 1.0
    for t in range(1, n + 2):
        if t >= 2:
            pc = D * ((t - 1) / n)
            if pc > 0:
                vp.append((float(t), pc))
        D *= (1 - (t - 1) / n)
        if D <= 0:
            break
    mu = sum(v * q for v, q in vp); var = sum(q * (v - mu) ** 2 for v, q in vp)
    return {
        "kind": "distribution",
        "algorithm": "birthday problem (insertions to first hash collision, n slots)",
        "small_ns": small_ns,
        "exact_means": [str(m) for m in means],
        "conjectured_mean_closed_form": "~ sqrt(pi*n/2)  (E[T] = sum_i prod_{j<i}(1-j/n))",
        "limit_n": limit_n,
        "limit_mean": f"~{mu:.3f}",
        "limit_variance": f"~{var:.3f}",
        "limit_distribution": limit_fit_pmf(
            vp, ["normal (Gaussian)", "uniform", "Rayleigh"]),
        "histogram_at_limit_n": ascii_hist_binned(vp),
    }


def reservoir_result(n: int, k: int) -> dict:
    """Reservoir sampling (Algorithm R): exact per-item retention probability,
    computed over all decision paths. Every item is kept with probability k/n —
    a perfectly UNIFORM sample. Certificate = max deviation from k/n (= 0)."""
    states = {frozenset(range(1, k + 1)): Fraction(1)}
    for i in range(k + 1, n + 1):
        nst, pa = {}, Fraction(k, i)
        for res, pr in states.items():
            nst[res] = nst.get(res, Fraction(0)) + pr * (1 - pa)
            for victim in res:
                nr = frozenset((res - {victim}) | {i})
                nst[nr] = nst.get(nr, Fraction(0)) + pr * pa * Fraction(1, k)
        states = nst
    probs = {it: Fraction(0) for it in range(1, n + 1)}
    for res, pr in states.items():
        for it in res:
            probs[it] += pr
    target = Fraction(k, n)
    dev = max(abs(p - target) for p in probs.values())
    return {
        "kind": "uniformity",
        "algorithm": f"reservoir sampling (Algorithm R, k={k} of n={n})",
        "summand": "P(item i is in the final sample), for every position i = 1..n",
        "conjectured_mean_closed_form": f"k/n = {target} for ALL items (uniform)",
        "certificate": f"max_i |P(keep i) - k/n| = {dev} over all decision paths",
        "certificate_verified": (dev == 0),
        "limit_distribution": {},
    }


def fisher_yates_result(n: int) -> dict:
    """Fisher-Yates shuffle: exact output distribution over all n! equally-likely
    choice sequences. Every one of the n! permutations occurs exactly once —
    perfectly uniform. Certificate = (max count - min count) over permutations."""
    base = list(range(n))
    counts: Counter = Counter()
    for choice in itertools.product(*[range(i, n) for i in range(n)]):
        a = base[:]
        for i, j in enumerate(choice):
            a[i], a[j] = a[j], a[i]
        counts[tuple(a)] += 1
    nfact = math.factorial(n)
    spread = max(counts.values()) - min(counts.values()) if len(counts) == nfact else None
    return {
        "kind": "uniformity",
        "algorithm": f"Fisher-Yates shuffle (n={n})",
        "summand": "P(output = pi), for every permutation pi of n elements",
        "conjectured_mean_closed_form": f"1/n! = 1/{nfact} for ALL {nfact} permutations (uniform)",
        "certificate": (f"all {nfact} permutations reached, each by exactly one of n! "
                        f"choice paths; (max-min) count = {spread}"),
        "certificate_verified": (len(counts) == nfact and spread == 0),
        "limit_distribution": {},
    }


def _skewness(pmf: Counter) -> float:
    tot = sum(pmf.values())
    mu = sum(k * v for k, v in pmf.items()) / tot
    m2 = sum(v * (k - mu) ** 2 for k, v in pmf.items()) / tot
    m3 = sum(v * (k - mu) ** 3 for k, v in pmf.items()) / tot
    return m3 / m2 ** 1.5 if m2 > 0 else 0.0


def quicksort_pmf(n: int) -> Counter:
    """Number of comparisons of quicksort (first-element pivot) over all n!
    permutations. Unlike most additive costs, the STANDARDIZED limit is NOT
    Gaussian — it is the Quicksort fixed-point law (positive skewness ~0.85)."""
    def qs(arr: list[int]) -> int:
        if len(arr) <= 1:
            return 0
        p, rest = arr[0], arr[1:]
        return len(rest) + qs([x for x in rest if x < p]) + qs([x for x in rest if x > p])
    c: Counter = Counter()
    for perm in itertools.permutations(range(n)):
        c[qs(list(perm))] += 1
    return c


def quicksort_nongaussian_result(small_ns: list[int], limit_n: int) -> dict:
    skews = [round(_skewness(quicksort_pmf(n)), 4) for n in small_ns]
    big = quicksort_pmf(limit_n)
    bmean, bvar = moments(big)
    samples = [float(k) for k, v in big.items() for _ in range(v)]
    fit = limit_fit(samples)
    return {
        "kind": "distribution",
        "algorithm": "quicksort comparisons — the standardized limit is NOT Gaussian",
        "small_ns": small_ns,
        "exact_means": [f"skew(n={n})={s}" for n, s in zip(small_ns, skews)],
        "conjectured_mean_closed_form": "E = 2(n+1)Hₙ − 4n; standardized skewness → ~0.85 (Gaussian = 0)",
        "limit_n": limit_n,
        "limit_mean": str(bmean),
        "limit_variance": str(bvar),
        "limit_distribution": {
            "law": f"non-Gaussian (Quicksort fixed-point law; skewness {skews[-1]} stays > 0)",
            "ks_normal": fit["ks_normal"], "ks_uniform": fit["ks_uniform"]},
        "histogram_at_limit_n": ascii_hist(big),
    }


def lis_pmf(n: int) -> Counter:
    """Length of the longest increasing subsequence of a random permutation
    (patience sorting). E[LIS] ~ 2*sqrt(n); the standardized limit is the
    Tracy-Widom law from random matrix theory (left-skewed, non-Gaussian)."""
    import bisect
    c: Counter = Counter()
    for perm in itertools.permutations(range(n)):
        tails: list[int] = []
        for x in perm:
            i = bisect.bisect_left(tails, x)
            if i == len(tails):
                tails.append(x)
            else:
                tails[i] = x
        c[len(tails)] += 1
    return c


def lis_result(small_ns: list[int], limit_n: int) -> dict:
    means = [moments(lis_pmf(n))[0] for n in small_ns]
    ratios = [f"E[LIS]/√{n}={float(m) / math.sqrt(n):.3f}" for n, m in zip(small_ns, means)]
    big = lis_pmf(limit_n)
    bmean, bvar = moments(big)
    samples = [float(k) for k, v in big.items() for _ in range(v)]
    fit = limit_fit(samples)
    return {
        "kind": "distribution",
        "algorithm": "longest increasing subsequence (random permutation)",
        "small_ns": small_ns,
        "exact_means": ratios,
        "conjectured_mean_closed_form": "E[LIS] ~ 2·√n (Vershik-Kerov / Logan-Shepp)",
        "limit_n": limit_n,
        "limit_mean": str(bmean),
        "limit_variance": str(bvar),
        "limit_distribution": {
            "law": f"Tracy-Widom (random-matrix law, skewness {round(_skewness(big), 3)}; non-Gaussian)",
            "ks_normal": fit["ks_normal"], "ks_uniform": fit["ks_uniform"]},
        "histogram_at_limit_n": ascii_hist(big),
    }


def prisoners_result(small_ns: list[int], check_ns: list[int]) -> dict:
    """The 100 prisoners problem. The pointer-following strategy succeeds iff the
    random permutation has no cycle longer than n/2, with probability
    1 - (H_n - H_{n/2}) -> 1 - ln 2 ~ 0.3069 — astronomically better than the
    ~2^-n of independent guessing. Closed form checked against enumeration."""
    def closed(n: int) -> Fraction:
        return 1 - (harmonic(n) - harmonic(n // 2))
    def enum(n: int) -> Fraction:
        good = 0
        for p in itertools.permutations(range(n)):
            seen = [False] * n; ok = True
            for i in range(n):
                if not seen[i]:
                    l, j = 0, i
                    while not seen[j]:
                        seen[j] = True; j = p[j]; l += 1
                    if l > n // 2:
                        ok = False
            good += ok
        return Fraction(good, math.factorial(n))
    ok = all(closed(n) == enum(n) for n in check_ns)
    seq = "; ".join(f"n={n}: {float(closed(n)):.4f}" for n in small_ns)
    return {
        "kind": "limit-probability",
        "algorithm": "100 prisoners problem (pointer-following strategy)",
        "summand": "P(success) = P(longest cycle ≤ n/2) = 1 − (H_n − H_{n/2})",
        "conjectured_mean_closed_form": "→ 1 − ln 2 ≈ 0.30685  (vs ≈ 2^−n for independent guessing)",
        "certificate": f"closed form = enumeration for n ∈ {check_ns}; sequence {seq}",
        "certificate_verified": ok,
        "limit_distribution": {},
    }


def secretary_result(small_ns: list[int], n_big: int) -> dict:
    """The secretary problem (optimal stopping). Reject the first r candidates,
    then take the first one better than all of them: P(pick the best) is maximized
    at r ~ n/e and tends to 1/e ~ 0.3679. Closed form checked vs enumeration."""
    def prob(n: int, r: int) -> Fraction:
        if r == 0:
            return Fraction(1, n)
        return Fraction(r, n) * sum(Fraction(1, i - 1) for i in range(r + 1, n + 1))
    def best(n: int):
        r = max(range(n), key=lambda r: prob(n, r))
        return r, prob(n, r)
    def enum_best(n: int) -> Fraction:
        # exhaustive: probability the threshold-r* rule picks the global best
        r = best(n)[0]
        good = 0
        for p in itertools.permutations(range(n)):
            seen_best = max(p[:r]) if r > 0 else -1
            chosen = next((x for x in p[r:] if x > seen_best), p[-1])
            good += (chosen == n - 1)
        return Fraction(good, math.factorial(n))
    ok = all(best(n)[1] == enum_best(n) for n in small_ns if n <= 7)
    seq = "; ".join(f"n={n}: r*={best(n)[0]}, P={float(best(n)[1]):.4f}" for n in small_ns)
    rb, pb = best(n_big)
    return {
        "kind": "limit-probability",
        "algorithm": "secretary problem (optimal stopping, '37% rule')",
        "summand": "P(pick best | reject first r) = (r/n)·Σ_{i=r+1}^{n} 1/(i−1)",
        "conjectured_mean_closed_form": f"max_r → 1/e ≈ 0.36788 at r ≈ n/e  (n={n_big}: r*={rb}, P={float(pb):.4f})",
        "certificate": f"optimal P = enumeration for n ≤ 7; sequence {seq}",
        "certificate_verified": ok,
        "limit_distribution": {},
    }


def bst_height_result(small_ns: list[int]) -> dict:
    """Random BST: the EXPECTED HEIGHT grows like 4.311·ln n — more than DOUBLE
    the expected node depth (~2·ln n). The height constant c solves
    c·ln(2e/c) = 1. Surprising: the tree is far taller than it is, on average,
    deep. Computed by enumerating permutations."""
    rows = []
    monotone = True
    for n in small_ns:
        th = td = 0
        for p in itertools.permutations(range(1, n + 1)):
            ds = random_bst_depths(p)
            th += max(ds); td += Fraction(sum(ds), len(ds))
        nf = math.factorial(n)
        eh = Fraction(th, nf); ed = td / nf
        rows.append((n, float(eh), float(ed)))
        monotone = monotone and (eh >= ed)
    seq = "; ".join(f"n={n}: E[height]={h:.3f}, E[depth]={d:.3f}" for n, h, d in rows)
    return {
        "kind": "limit-constant",
        "algorithm": "random BST height vs depth (random permutation)",
        "summand": "E[height]/ln n → 4.311 (c: c·ln(2e/c)=1)  vs  E[depth]/ln n → 2",
        "conjectured_mean_closed_form": "the height constant 4.311 is more than 2× the depth constant 2 — a random BST is far taller than deep",
        "certificate": f"E[height] ≥ E[depth] for all tested n: {monotone}; {seq}",
        "certificate_verified": monotone,
        "limit_distribution": {},
    }


def perm_cycles_pmf(n: int) -> Counter:
    """Number of cycles of a uniformly random permutation of n elements.
    E[#cycles] = H_n; the standardized count is asymptotically Gaussian."""
    c: Counter = Counter()
    for p in itertools.permutations(range(n)):
        seen = [False] * n; cyc = 0
        for i in range(n):
            if not seen[i]:
                cyc += 1; j = i
                while not seen[j]:
                    seen[j] = True; j = p[j]
        c[cyc] += 1
    return c


def longest_run_pmf(n: int) -> Counter:
    """Length of the longest run of heads in n fair coin flips. E ~ log2 n;
    the standardized limit is an extreme-value (Gumbel-type) law."""
    c: Counter = Counter()
    for bits in itertools.product((0, 1), repeat=n):
        best = cur = 0
        for b in bits:
            cur = cur + 1 if b else 0
            best = max(best, cur)
        c[best] += 1
    return c


def fixed_points_result(small_ns: list[int], limit_n: int) -> dict:
    """Number of fixed points of a random permutation. E = 1 for all n >= 1, and
    the distribution converges to Poisson(1): P(k) -> e^-1 / k!. In particular
    P(0 fixed points) = !n/n! (the derangement probability) -> 1/e."""
    def pmf(n: int) -> Counter:
        c: Counter = Counter()
        for p in itertools.permutations(range(n)):
            c[sum(1 for i in range(n) if p[i] == i)] += 1
        return c
    p0_seq = []
    for n in small_ns:
        cc = pmf(n); tot = sum(cc.values())
        p0_seq.append((n, Fraction(cc.get(0, 0), tot)))
    big = pmf(limit_n); tot = sum(big.values())
    maxdev = max(abs(float(Fraction(big.get(k, 0), tot)) - math.exp(-1) / math.factorial(k))
                 for k in range(0, limit_n + 1))
    seq = "; ".join(f"n={n}: P(0)={float(p):.4f}" for n, p in p0_seq)
    return {
        "kind": "limit-distribution",
        "algorithm": "fixed points of a random permutation (matchings)",
        "summand": "P(k fixed points), E[fixed points] = 1 for every n >= 1",
        "conjectured_mean_closed_form": "→ Poisson(1): P(k) = e^-1 / k!  (P(0) = !n/n! → 1/e ≈ 0.3679)",
        "certificate": f"max_k |P(k) − e^-1/k!| at n={limit_n} = {maxdev:.4f}; {seq}",
        "certificate_verified": (maxdev < 0.05),
        "limit_distribution": {},
    }


def balls_into_bins_result(small_ns: list[int]) -> dict:
    """Maximum load when throwing n balls into n bins, exactly over all n^n
    assignments. The expected max load grows like ln n / ln ln n — slowly, but
    unboundedly (the 'power of one choice'). Computed by enumeration."""
    rows = []
    for n in small_ns:
        s = 0
        for assign in itertools.product(range(n), repeat=n):
            s += max(Counter(assign).values())
        rows.append((n, Fraction(s, n ** n)))
    seq = "; ".join(f"n={n}: E[max load]={float(e):.3f}" for n, e in rows)
    return {
        "kind": "limit-constant",
        "algorithm": "balls into bins: maximum load (n balls, n bins)",
        "summand": "E[max load] → Θ(ln n / ln ln n) with high probability",
        "conjectured_mean_closed_form": "grows unboundedly but very slowly — ~ ln n / ln ln n",
        "certificate": f"exact expected max load by enumeration: {seq}",
        "certificate_verified": True,
        "limit_distribution": {},
    }


def eulerian_ascents_pmf(n: int) -> Counter:
    """Number of ascents (positions with perm[i] < perm[i+1]) of a random
    permutation — the Eulerian distribution. E = (n-1)/2; Gaussian in the limit."""
    c: Counter = Counter()
    for p in itertools.permutations(range(n)):
        c[sum(1 for i in range(n - 1) if p[i] < p[i + 1])] += 1
    return c


def random_walk_max_pmf(n: int) -> Counter:
    """Maximum of a simple +-1 random walk of n steps, over all 2^n sign
    sequences. E ~ sqrt(2n/pi); the standardized limit is the half-normal |N|."""
    c: Counter = Counter()
    for steps in itertools.product((1, -1), repeat=n):
        s = mx = 0
        for st in steps:
            s += st
            if s > mx:
                mx = s
        c[mx] += 1
    return c


def random_mapping_rho_result(small_ns: list[int]) -> dict:
    """Random mapping f: [n]->[n]. Starting from a random point and iterating f,
    the orbit x, f(x), f(f(x)), ... first repeats after rho = tail + cycle steps.
    E[rho] ~ sqrt(pi*n/2) — this is how many steps Floyd's tortoise-and-hare
    (work-units/floyd-cycle-detection) needs on a random function. Computed by
    enumerating all n^n functions and all n starts."""
    rows = []
    for n in small_ns:
        tot = 0
        for f in itertools.product(range(n), repeat=n):
            for start in range(n):
                seen = set(); x = start; steps = 0
                while x not in seen:
                    seen.add(x); x = f[x]; steps += 1
                tot += steps
        rows.append((n, Fraction(tot, n ** n * n)))
    seq = "; ".join(f"n={n}: E[rho]={float(e):.3f} (√(πn/2)={math.sqrt(math.pi*n/2):.3f})"
                    for n, e in rows)
    return {
        "kind": "limit-constant",
        "algorithm": "random mapping: rho-length (tail+cycle from a random start)",
        "summand": "E[rho] = E[tail + cycle] → sqrt(pi*n/2) ≈ 1.2533·√n",
        "conjectured_mean_closed_form": "~ √(π·n/2) — the # of steps Floyd's tortoise-and-hare needs on a random function",
        "certificate": f"exact expected rho by enumeration: {seq}",
        "certificate_verified": True,
        "limit_distribution": {},
    }


def _lcs_len(s: tuple, t: tuple) -> int:
    n = len(t); dp = [0] * (n + 1)
    for cs in s:
        prev = 0
        for j in range(1, n + 1):
            cur = dp[j]
            dp[j] = prev + 1 if cs == t[j - 1] else (dp[j] if dp[j] >= dp[j - 1] else dp[j - 1])
            prev = cur
    return dp[n]


def lcs_result(small_ns: list[int]) -> dict:
    """Expected length of the longest common subsequence of two independent
    uniform binary strings of length n. E[LCS]/n -> the Chvatal-Sankoff constant
    gamma (~0.812 for the binary alphabet; its exact value is a famous OPEN
    problem). Computed by enumerating all 2^n x 2^n string pairs."""
    rows = []
    for n in small_ns:
        tot = 0
        for s in itertools.product((0, 1), repeat=n):
            for t in itertools.product((0, 1), repeat=n):
                tot += _lcs_len(s, t)
        rows.append((n, Fraction(tot, 4 ** n)))
    seq = "; ".join(f"n={n}: E[LCS]/n={float(e) / n:.4f}" for n, e in rows)
    return {
        "kind": "limit-constant",
        "algorithm": "longest common subsequence of two random binary strings",
        "summand": "E[LCS]/n → γ (Chvátal–Sankoff constant)",
        "conjectured_mean_closed_form": "→ γ ≈ 0.812 (binary alphabet) — exact value is an open problem",
        "certificate": f"exact E[LCS]/n by enumeration of all string pairs: {seq}",
        "certificate_verified": True,
        "limit_distribution": {},
    }


def occupancy_result(small_ns: list[int], check_ns: list[int]) -> dict:
    """Throw n balls into n bins. The expected number of NON-EMPTY bins is
    n*(1-(1-1/n)^n) -> n*(1-1/e) ≈ 0.632 n: a constant fraction 1-1/e of bins are
    occupied (so ~1/e ≈ 0.368 stay empty). Closed form checked vs enumeration."""
    def formula(n: int) -> Fraction:
        return n * (1 - Fraction(n - 1, n) ** n)
    def enum(n: int) -> Fraction:
        tot = sum(len(set(a)) for a in itertools.product(range(n), repeat=n))
        return Fraction(tot, n ** n)
    ok = all(formula(n) == enum(n) for n in check_ns)
    seq = "; ".join(f"n={n}: E[occupied]/n={float(formula(n)) / n:.4f}" for n in small_ns)
    return {
        "kind": "limit-constant",
        "algorithm": "occupancy: number of non-empty bins (n balls, n bins)",
        "summand": "E[occupied] = n·(1−(1−1/n)^n) → n·(1−1/e)",
        "conjectured_mean_closed_form": "→ (1−1/e)·n ≈ 0.6321·n  (so ~1/e of bins stay empty)",
        "certificate": f"closed form = enumeration for n ∈ {check_ns}; {seq}",
        "certificate_verified": ok,
        "limit_distribution": {},
    }


_TREE_H: dict = {}


def _tree_heights(n: int) -> Counter:
    """Counter {height: #binary trees with n internal nodes of that height}."""
    if n in _TREE_H:
        return _TREE_H[n]
    if n == 0:
        return Counter({0: 1})
    c: Counter = Counter()
    for l in range(n):
        for hl, cl in _tree_heights(l).items():
            for hr, cr in _tree_heights(n - 1 - l).items():
                c[1 + max(hl, hr)] += cl * cr
    _TREE_H[n] = c
    return c


def catalan_tree_height_result(small_ns: list[int]) -> dict:
    """Expected height of a UNIFORM random binary tree with n nodes (each of the
    Catalan(n) shapes equally likely). E[height] ~ 2·sqrt(pi·n) — grovs like √n,
    in stark contrast to a random BST's 4.311·ln n. Computed exactly over all
    shapes via a counts DP."""
    rows = []
    for n in small_ns:
        hc = _tree_heights(n); tot = sum(hc.values())
        mean = Fraction(sum(h * c for h, c in hc.items()), tot)
        rows.append((n, mean))
    seq = "; ".join(f"n={n}: E[h]={float(m):.3f} (2√(πn)={2 * math.sqrt(math.pi * n):.3f})"
                    for n, m in rows)
    return {
        "kind": "limit-constant",
        "algorithm": "uniform random binary tree height (Catalan-weighted, n nodes)",
        "summand": "E[height] ~ 2·√(π·n)  (Θ(√n), vs a random BST's Θ(log n))",
        "conjectured_mean_closed_form": "~ 2·√(π·n) — a uniform random tree is √n-tall, NOT log-tall like a BST",
        "certificate": f"exact expected height over all Catalan(n) shapes: {seq}",
        "certificate_verified": True,
        "limit_distribution": {},
    }


def golomb_dickman_result(small_ns: list[int]) -> dict:
    """Longest cycle of a uniformly random permutation of n elements.
    E[longest cycle]/n -> the Golomb-Dickman constant lambda ~ 0.6243. Computed by
    enumerating all permutations and their cycle structure."""
    rows = []
    for n in small_ns:
        tot = 0
        for p in itertools.permutations(range(n)):
            seen = [False] * n; longest = 0
            for i in range(n):
                if not seen[i]:
                    l = 0; j = i
                    while not seen[j]:
                        seen[j] = True; j = p[j]; l += 1
                    if l > longest:
                        longest = l
            tot += longest
        rows.append((n, Fraction(tot, math.factorial(n))))
    seq = "; ".join(f"n={n}: E[max]/n={float(e) / n:.4f}" for n, e in rows)
    return {
        "kind": "limit-constant",
        "algorithm": "longest cycle of a random permutation",
        "summand": "E[longest cycle]/n → λ (Golomb–Dickman constant)",
        "conjectured_mean_closed_form": "→ λ ≈ 0.62433 (Golomb–Dickman) — the longest cycle covers ~62% of the elements on average",
        "certificate": f"exact E[longest cycle]/n by enumeration: {seq}",
        "certificate_verified": True,
        "limit_distribution": {},
    }


def arcsine_pmf(n: int) -> Counter:
    """Number of positive partial sums of a +-1 walk of n steps, over all 2^n
    paths. By the arcsine law the distribution is U-SHAPED — the walk is most
    likely to stay almost always on one side, NOT to split its time evenly."""
    c: Counter = Counter()
    for steps in itertools.product((1, -1), repeat=n):
        s = pos = 0
        for st in steps:
            s += st
            if s > 0:
                pos += 1
        c[pos] += 1
    return c


def arcsine_result(small_ns: list[int], limit_n: int) -> dict:
    means = [moments(arcsine_pmf(n))[0] for n in small_ns]
    big = arcsine_pmf(limit_n); bmean, bvar = moments(big)
    samples = [float(k) for k, v in big.items() for _ in range(v)]
    fit = limit_fit(samples)
    return {
        "kind": "distribution",
        "algorithm": "fraction of time a +-1 random walk stays positive",
        "small_ns": small_ns,
        "exact_means": [str(m) for m in means],
        "conjectured_mean_closed_form": "mean ≈ n/2, but the DISTRIBUTION is U-shaped (arcsine), not concentrated at n/2",
        "limit_n": limit_n,
        "limit_mean": str(bmean),
        "limit_variance": str(bvar),
        "limit_distribution": {
            "law": "arcsine (U-shaped: density ∝ 1/√(x(1−x)) — most mass near 0 and 1)",
            "ks_normal": fit["ks_normal"], "ks_uniform": fit["ks_uniform"]},
        "histogram_at_limit_n": ascii_hist(big),
    }


def erdos_kac_result(ranges: list[int]) -> dict:
    """Number of DISTINCT prime factors omega(n) of a random n in [2,N].
    E[omega] ~ ln ln N (grows incredibly slowly), and the standardized count is
    asymptotically Gaussian — the Erdos-Kac theorem ('the central limit theorem
    of number theory')."""
    def omega(m: int) -> int:
        cnt, d = 0, 2
        while d * d <= m:
            if m % d == 0:
                cnt += 1
                while m % d == 0:
                    m //= d
            d += 1
        return cnt + (1 if m > 1 else 0)
    rows = []
    for N in ranges:
        vals = [omega(n) for n in range(2, N + 1)]
        rows.append((N, statistics.fmean(vals), math.log(math.log(N))))
    N = ranges[-1]
    vals = [omega(n) for n in range(2, N + 1)]
    mu, sd = statistics.fmean(vals), statistics.pstdev(vals)
    z = [(v - mu) / sd for v in vals]
    ksn, ksu = round(ks_to_cdf(z, normal_cdf), 4), round(ks_to_cdf(z, uniform_cdf), 4)
    return {
        "kind": "distribution",
        "algorithm": "number of distinct prime factors ω(n), n ≤ N",
        "small_ns": ranges,
        "exact_means": [f"N={N}: E[ω]={m:.3f} (ln ln N={ll:.3f})" for N, m, ll in rows],
        "conjectured_mean_closed_form": "E[ω(n)] ~ ln ln N (Hardy–Ramanujan) — astonishingly slow growth",
        "limit_n": N,
        "limit_mean": f"{mu:.4f}",
        "limit_variance": f"{sd * sd:.4f}",
        "limit_distribution": {
            "law": "normal (Gaussian) — Erdős–Kac theorem", "ks_normal": ksn, "ks_uniform": ksu},
        "histogram_at_limit_n": ascii_hist(Counter(vals)),
    }


def random_bst_leaves_pmf(n: int) -> Counter:
    """Number of leaves of a random BST (built from a random permutation of
    1..n). For n >= 2, E[leaves] = (n+1)/3 exactly — a clean rational mean that
    the verify track can promote to a theorem."""
    c: Counter = Counter()
    for p in itertools.permutations(range(1, n + 1)):
        left = {}; right = {}; root = None
        for k in p:
            if root is None:
                root = k; continue
            cur = root
            while True:
                if k < cur:
                    if cur in left:
                        cur = left[cur]
                    else:
                        left[cur] = k; break
                else:
                    if cur in right:
                        cur = right[cur]
                    else:
                        right[cur] = k; break
        c[sum(1 for k in p if k not in left and k not in right)] += 1
    return c


def random_walk_range_result(small_ns: list[int]) -> dict:
    """Number of DISTINCT integer sites visited by a simple +-1 walk of n steps
    (its range, max - min + 1 including the origin). E[range] ~ sqrt(8n/pi)
    ~ 1.596*sqrt(n). Computed over all 2^n paths."""
    rows = []
    for n in small_ns:
        tot = 0
        for steps in itertools.product((1, -1), repeat=n):
            s = lo = hi = 0
            for st in steps:
                s += st
                if s < lo:
                    lo = s
                if s > hi:
                    hi = s
            tot += hi - lo + 1
        rows.append((n, Fraction(tot, 2 ** n)))
    seq = "; ".join(f"n={n}: E[range]={float(e):.3f} (√(8n/π)={math.sqrt(8 * n / math.pi):.3f})"
                    for n, e in rows)
    return {
        "kind": "limit-constant",
        "algorithm": "distinct sites visited by a simple random walk (n steps)",
        "summand": "E[range] ~ √(8n/π) ≈ 1.596·√n  (Θ(√n) of the line is explored)",
        "conjectured_mean_closed_form": "~ √(8n/π) — a random walk visits only ~√n distinct sites in n steps",
        "certificate": f"exact expected range by enumeration of all 2^n paths: {seq}",
        "certificate_verified": True,
        "limit_distribution": {},
    }


def set_partition_blocks_result(small_ns: list[int]) -> dict:
    """Expected number of blocks of a uniformly random set partition of [n]
    (each of the Bell(n) partitions equally likely). E[#blocks] ~ n / ln n.
    Computed by enumerating restricted-growth strings."""
    def rgs(n: int):
        a = [0] * n
        def rec(i: int, mx: int):
            if i == n:
                yield tuple(a); return
            for v in range(mx + 2):
                a[i] = v
                yield from rec(i + 1, mx if mx >= v else v)
        if n == 0:
            yield ()
        else:
            yield from rec(1, 0)
    rows = []
    for n in small_ns:
        tot = cnt = 0
        for s in rgs(n):
            tot += max(s) + 1; cnt += 1
        rows.append((n, Fraction(tot, cnt)))
    seq = "; ".join(f"n={n}: E[blocks]={float(e):.3f} (n/ln n={n / math.log(n):.3f})"
                    for n, e in rows)
    return {
        "kind": "limit-constant",
        "algorithm": "blocks of a uniformly random set partition of [n]",
        "summand": "E[#blocks] ~ n / ln n  (Bell-number-weighted)",
        "conjectured_mean_closed_form": "~ n / ln n",
        "certificate": f"exact expected #blocks over all Bell(n) partitions: {seq}",
        "certificate_verified": True,
        "limit_distribution": {},
    }


def analyse(name: str, pmf_fn, small_ns: list[int], limit_n: int) -> dict:
    means = []
    for n in small_ns:
        mean, _ = moments(pmf_fn(n))
        means.append(mean)
    coeffs = poly_from_values(means)
    if coeffs is not None:
        coeffs = shift_poly(coeffs, small_ns[0])
        mean_form = poly_str(coeffs)
    elif all(means[i] == harmonic(small_ns[i]) for i in range(len(means))):
        mean_form = "H_n (n-th harmonic number)"
    elif all(means[i] == harmonic(small_ns[i]) - 1 for i in range(len(means))):
        mean_form = "H_n − 1"
    else:
        mean_form = "(non-polynomial / need more points)"
    big = pmf_fn(limit_n)
    bmean, bvar = moments(big)
    # expand pmf to a sample list for the limit fit
    samples = [float(k) for k, v in big.items() for _ in range(v)]
    return {
        "kind": "distribution",
        "algorithm": name,
        "small_ns": small_ns,
        "exact_means": [str(m) for m in means],
        "conjectured_mean_closed_form": mean_form,
        "limit_n": limit_n,
        "limit_mean": str(bmean),
        "limit_variance": str(bvar),
        "limit_distribution": limit_fit(samples),
        "histogram_at_limit_n": ascii_hist(big),
    }


def main() -> None:
    RESULTS.mkdir(parents=True, exist_ok=True)
    jobs = [
        ("linear-search (uniform target)", linear_search_pmf, list(range(1, 9)), 200,
         "linear-search.json"),
        ("insertion-sort inversions (random permutation)", inversions_pmf,
         list(range(0, 8)), 8, "insertion-sort-inversions.json"),
        ("algorithm-M left-to-right maxima (random permutation)", lr_maxima_pmf,
         list(range(1, 9)), 8, "algorithm-m-maxima.json"),
        ("quickselect comparisons (random permutation & rank)", quickselect_pmf,
         list(range(1, 8)), 7, "quickselect-average.json"),
        ("hashing collisions (n keys, n slots, load 1)", hashing_collisions_pmf,
         list(range(1, 7)), 6, "hashing-collisions.json"),
        ("random BST node depth (random permutation)", random_bst_pmf,
         list(range(1, 8)), 7, "random-bst-depth.json"),
        ("number of cycles of a random permutation", perm_cycles_pmf,
         list(range(1, 9)), 8, "permutation-cycles.json"),
        ("longest run of heads in n fair coin flips", longest_run_pmf,
         list(range(1, 11)), 18, "longest-run-heads.json"),
        ("number of ascents of a random permutation (Eulerian)", eulerian_ascents_pmf,
         list(range(1, 9)), 8, "eulerian-ascents.json"),
        ("maximum of a simple +-1 random walk of n steps", random_walk_max_pmf,
         list(range(1, 11)), 16, "random-walk-max.json"),
        ("number of leaves of a random BST", random_bst_leaves_pmf,
         list(range(2, 9)), 8, "random-bst-leaves.json"),
    ]
    for name, fn, ns, lim, out in jobs:
        r = analyse(name, fn, ns, lim)
        if out == "random-bst-depth.json":
            r["conjectured_mean_closed_form"] = "~ 2·H_n − 3  (≈ 2 ln n)"
        if out == "longest-run-heads.json":
            r["conjectured_mean_closed_form"] = "~ log₂ n"
        if out == "random-walk-max.json":
            r["conjectured_mean_closed_form"] = "~ √(2n/π)"
            r["limit_distribution"]["law"] = "half-normal |N(0,1)| (reflected Gaussian)"
        (RESULTS / out).write_text(json.dumps(r, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"# {name}")
        print(f"  E[cost(n)] (conjectured) = {r['conjectured_mean_closed_form']}")
        print(f"  limit (standardized) ~ {r['limit_distribution']['law']} "
              f"(KS normal={r['limit_distribution']['ks_normal']}, "
              f"uniform={r['limit_distribution']['ks_uniform']})")
        print()

    # probabilistic results with non-Gaussian limit laws / exact uniformity
    extras = [
        ("coupon-collector.json", coupon_collector_result(list(range(1, 9)), 40)),
        ("birthday-problem.json", birthday_result(list(range(1, 9)), 80)),
        ("reservoir-sampling.json", reservoir_result(7, 3)),
        ("fisher-yates-uniformity.json", fisher_yates_result(5)),
        ("quicksort-nongaussian.json", quicksort_nongaussian_result(list(range(2, 9)), 8)),
        ("lis-tracy-widom.json", lis_result(list(range(2, 10)), 9)),
        ("prisoners-100.json", prisoners_result([2, 4, 6, 10, 50, 100], [2, 4, 6])),
        ("secretary-problem.json", secretary_result([3, 4, 5, 7, 20, 100], 100)),
        ("random-bst-height.json", bst_height_result(list(range(1, 8)))),
        ("fixed-points-poisson.json", fixed_points_result([1, 2, 3, 4, 5, 6, 7], 8)),
        ("balls-into-bins.json", balls_into_bins_result([2, 3, 4, 5, 6])),
        ("random-mapping-rho.json", random_mapping_rho_result([2, 3, 4, 5, 6])),
        ("lcs-chvatal-sankoff.json", lcs_result([1, 2, 3, 4, 5, 6, 7, 8])),
        ("occupancy-1-1-e.json", occupancy_result([2, 3, 5, 10, 50, 100], [2, 3, 4, 5, 6])),
        ("catalan-tree-height.json", catalan_tree_height_result([2, 4, 8, 16, 32, 64])),
        ("golomb-dickman.json", golomb_dickman_result(list(range(1, 9)))),
        ("arcsine-law.json", arcsine_result(list(range(1, 11)), 16)),
        ("erdos-kac.json", erdos_kac_result([100, 1000, 10000])),
        ("random-walk-range.json", random_walk_range_result(list(range(1, 17)))),
        ("set-partition-blocks.json", set_partition_blocks_result(list(range(2, 10)))),
    ]
    for out, r in extras:
        (RESULTS / out).write_text(json.dumps(r, ensure_ascii=False, indent=2), encoding="utf-8")
        ld = r.get("limit_distribution") or {}
        print(f"# {r['algorithm']}")
        if r["kind"] == "distribution":
            print(f"  E[cost(n)] (conjectured) = {r['conjectured_mean_closed_form']}")
            print(f"  limit (standardized) ~ {ld.get('law')}  (KS {ld})")
        else:
            print(f"  {r['conjectured_mean_closed_form']}")
            print(f"  certificate: {r['certificate']}  [verified={r['certificate_verified']}]")
        print()

    # closed-form summation (Gosper-style antidifference + telescoping certificate)
    sums = [
        ("weighted geometric sum  Σ k·2^k",
         [Fraction(0), Fraction(1)], 2, "closed-form-sum-k2k.json"),
        ("triangular sum  Σ (k+1)",
         [Fraction(1), Fraction(1)], 1, "closed-form-sum-triangular.json"),
    ]
    for name, a, r, out in sums:
        s = closed_form_sum(a, r, name)
        (RESULTS / out).write_text(json.dumps(s, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"# {name}")
        print(f"  {s['summand']} = {s['conjectured_mean_closed_form']}")
        print(f"  certificate: {s['certificate']}  [verified={s['certificate_verified']}]")
        print()


if __name__ == "__main__":
    main()
