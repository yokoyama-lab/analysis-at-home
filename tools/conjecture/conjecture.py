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
    ]
    for name, fn, ns, lim, out in jobs:
        r = analyse(name, fn, ns, lim)
        if out == "random-bst-depth.json":
            r["conjectured_mean_closed_form"] = "~ 2·H_n − 3  (≈ 2 ln n)"
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
