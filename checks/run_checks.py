"""Golden-value checks: the numbers printed in the paper against the numerics and the
proven closed forms.

Run from the repository root:  python checks/run_checks.py
Exit status 0 if every check passes. Each line names the paper label it checks.

Every quantity here is an exact rational: with lambda = 1 all matrix elements are 0 or +-1,
so the traces are integers and mu_l = Tr(H^l)/D is compared as a Fraction. The closed forms
are the statements proved in lean/ (see docs/correspondence.tsv); the checks confirm that
the numerics and the formulas agree, which is the cross-tier check of docs/framework.md.
The slow cases (n = 6 at L = 5, finite-U spectra) are covered by evidence records instead.
"""
import os
import sys
import time

# The matrices here are small: one BLAS thread is fastest, and a many-core OpenBLAS default
# (32 threads on a 16-core Linux box) made the run six times slower. Set before numpy loads.
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from uinf_traces_sparse import build_Uinf_H_sparse  # noqa: E402
from sw_correction import sw_moments  # noqa: E402
import sector_theory as st  # noqa: E402
from frozen_check import problems as frozen_problems  # noqa: E402
from hinf_local import (apply_H, basis, cfg, four_cycles, h2_diag, h4_diag, kagome_neighbors,  # noqa: E402
                        small_graphs, torus_neighbors)
import mu4_closed_form as m4c  # noqa: E402

RESULTS = []
BETA_SPREAD = {4: "0.14", 5: "0.06", 6: "0.03"}   # printed in the paper (sec:SW), percent


def exact(x, what):
    """An integer-valued float trace, as an int."""
    r = round(x)
    if abs(x - r) > 1e-6:
        raise ValueError(f"{what}: trace {x!r} is not an integer")
    return r


def fmt(v):
    return "(" + ", ".join(map(str, v)) + ")" if isinstance(v, tuple) else str(v)


def check(label, what, got, expected):
    ok = got == expected
    RESULTS.append(ok)
    print(f"{'PASS' if ok else 'FAIL'}  {label:<16} {what:<44} got {fmt(got)}  expected {fmt(expected)}")


def uinf_moments(L, nup, ndn):
    """Exact mu_2 and mu_4 of H_inf = P0 H_t P0 at lambda = 1."""
    H, D = build_Uinf_H_sparse(L, nup, ndn, lam=1.0)
    H2 = H @ H
    tr2 = exact(H2.diagonal().sum(), "Tr H^2")
    tr4 = exact(H2.multiply(H2).sum(), "Tr H^4")
    return Fraction(tr2, D), Fraction(tr4, D)


def mu2_formula_torus(L, n):
    """Lean: secondMomentTorus / secondMomentHubbardTorus at t = 1."""
    N = L * L
    return Fraction(4 * n * (N - n), N - 1)


def torus_band_L4():
    """The 16 energies -2(cos q1 + cos q2) at L = 4; the cosines are exactly 1, 0, -1, 0."""
    c = [1, 0, -1, 0]
    return [-2 * (c[a] + c[b]) for a in range(4) for b in range(4)]


def sample_moments(eps, k):
    """mu_2, mu_4 of the sum of k of the values eps drawn without replacement."""
    sums = [sum(s) for s in combinations(eps, k)]
    D = len(sums)
    return Fraction(sum(x ** 2 for x in sums), D), Fraction(sum(x ** 4 for x in sums), D)


def fpc_formulas(eps, k):
    """Lean: finitePopulationVariance and finitePopulationFourthMoment."""
    N = len(eps)
    P2 = sum(x ** 2 for x in eps)
    P4 = sum(x ** 4 for x in eps)

    def p(m):
        num = den = 1
        for i in range(m):
            num *= k - i
            den *= N - i
        return Fraction(num, den)

    mu2 = Fraction(k) * Fraction(P2) / N * (N - k) / (N - 1)
    mu4 = P4 * (p(1) - 7 * p(2) + 12 * p(3) - 6 * p(4)) + 3 * P2 ** 2 * (p(2) - 2 * p(3) + p(4))
    return mu2, mu4


def sector_dimension(N, a, b, k):
    """Count pairs (up set, down set) with exactly k common sites, by enumeration."""
    downs = [frozenset(s) for s in combinations(range(N), b)]
    return sum(1 for u in combinations(range(N), a) for d in downs if len(d & set(u)) == k)


def main():
    t0 = time.time()

    # Frozen claims: the register equals the freeze record plus the drift log (framework §6)
    check("register", "frozen rows vs frozen.tsv + drift-log.tsv", frozen_problems(), [])

    # Sector dimensions (Lean: sectorDimensionsQuoted)
    for (L, a, b, k, val) in [(4, 2, 2, 0, 10920), (4, 2, 2, 1, 3360), (4, 2, 2, 2, 120),
                              (5, 2, 1, 0, 6900), (5, 2, 1, 1, 600)]:
        N = L * L
        check("sec:fewbody", f"sector dim L={L} ({a},{b}) k={k} enumerated",
              sector_dimension(N, a, b, k), val)
        check("sec:fewbody", f"sector dim L={L} ({a},{b}) k={k} formula",
              comb(N, a) * comb(a, k) * comb(N - a, b - k), val)

    # Table tab:mu2verify (Lean: secondMomentTorus)
    for (L, n, val) in [(3, 2, Fraction(7)), (4, 3, Fraction(52, 5)), (4, 4, Fraction(64, 5)),
                        (5, 4, Fraction(14)), (6, 4, Fraction(512, 35))]:
        mu2, _ = uinf_moments(L, n, 0)
        check("tab:mu2verify", f"mu2(inf) L={L} n={n} sparse trace", mu2, val)
        check("tab:mu2verify", f"mu2(inf) L={L} n={n} theorem", mu2_formula_torus(L, n), val)

    # Table tab:mu4exact (mu2 spin-blind, mu4 exact rationals)
    table4 = [((2, 0), Fraction(112, 15), Fraction(2176, 15)),
              ((1, 1), Fraction(112, 15), Fraction(2272, 15)),
              ((3, 0), Fraction(52, 5), Fraction(9976, 35)),
              ((2, 1), Fraction(52, 5), Fraction(10348, 35)),
              ((4, 0), Fraction(64, 5), Fraction(197632, 455)),
              ((3, 1), Fraction(64, 5), Fraction(203536, 455)),
              ((2, 2), Fraction(64, 5), Fraction(15808, 35))]
    mu4_L4 = {}
    for (comp, m2, m4) in table4:
        mu2, mu4 = uinf_moments(4, *comp)
        mu4_L4[comp] = mu4
        check("tab:mu4exact", f"mu2(inf) L=4 {comp}", mu2, m2)
        check("tab:mu4exact", f"mu4(inf) L=4 {comp}", mu4, m4)
        check("tab:mu4exact", f"mu2(inf) L=4 {comp} vs theorem", mu2, mu2_formula_torus(4, sum(comp)))
    # sec:fewbody#shape: the N_d=0 band of (1,1) at L=5 against the free 4D lattice (mu2 = 8,
    # excess kurtosis -3/8 for L >= 5): mu2 = 23/3, mu4 = 461/3, excess kurtosis -204/529
    m2, m4 = uinf_moments(5, 1, 1)
    check("sec:fewbody", "L=5 (1,1): N_d=0 band mu2, mu4, excess kurtosis", (m2, m4, m4 / m2 ** 2 - 3),
          (Fraction(23, 3), Fraction(461, 3), Fraction(-204, 529)))
    # n = 4: the two slopes in P_same agree (P_same = 6, 3, 2 for (4,0), (3,1), (2,2))
    s1 = (mu4_L4[(4, 0)] - mu4_L4[(3, 1)]) / (6 - 3)
    s2 = (mu4_L4[(3, 1)] - mu4_L4[(2, 2)]) / (3 - 2)
    check("sec:mu4exchange", "n=4 L=4 slopes in P_same agree", s1, s2)

    # Table tab:fpcexact: U = 0, one species, by enumeration and by the proven closed forms
    eps = torus_band_L4()
    check("tab:fpcexact", "L=4 band: sum, P2, P4", (sum(eps), sum(x * x for x in eps),
                                                   sum(x ** 4 for x in eps)), (0, 64, 640))
    for (k, m2, m4) in [(2, Fraction(112, 15), Fraction(2176, 15)),
                        (3, Fraction(52, 5), Fraction(9976, 35)),
                        (4, Fraction(64, 5), Fraction(197632, 455))]:
        e2, e4 = sample_moments(eps, k)
        f2, f4 = fpc_formulas(eps, k)
        check("tab:fpcexact", f"U=0 k={k} mu2 enumerated", e2, m2)
        check("tab:fpcexact", f"U=0 k={k} mu4 enumerated", e4, m4)
        check("tab:fpcexact", f"U=0 k={k} mu2, mu4 closed forms", (f2, f4), (m2, m4))
        # one species: U = 0 and U = inf are the same operator
        check("sec:fermistats", f"k={k} one species: mu4(U=0) = mu4(U=inf)", e4, mu4_L4[(k, 0)])

    # alpha(N, 2) = mu4(2,0) - mu4(1,1) (P_same = 1 vs 0): -64/(N-1) for L >= 5, -32/5 at L = 4
    for L in [4, 5, 6, 7]:
        N = L * L
        alpha = uinf_moments(L, 2, 0)[1] - uinf_moments(L, 1, 1)[1]
        expected = Fraction(-32, 5) if L == 4 else Fraction(-64, N - 1)
        check("sec:mu4exchange", f"alpha(N,2) at L={L}", alpha, expected)

    # Schrieffer-Wolff cross term: Tr(T0 V) = 0 for L >= 4 (triangle-free), nonzero at L = 3
    for (L, nup, ndn) in [(4, 2, 2), (4, 3, 1), (5, 2, 1)]:
        m = sw_moments(L, nup, ndn, lam=1.0)
        check("sec:SW", f"Tr(T0 V) L={L} ({nup},{ndn})", exact(m["tr_T0V"], "Tr T0 V"), 0)
    m = sw_moments(3, 1, 1, lam=1.0)
    got = exact(m["tr_T0V"], "Tr T0 V") != 0
    check("sec:SW", "Tr(T0 V) L=3 (1,1) is nonzero", got, True)

    # ---- Rows of docs/correspondence.tsv that had no located evidence ----

    # sec:mu2theorem#nonregular: mu2 on non-regular graphs, by explicit H_inf
    graphs = {
        "open chain, 7 sites": [[j for j in (i - 1, i + 1) if 0 <= j < 7] for i in range(7)],
        "star, 6 sites": [[1, 2, 3, 4, 5]] + [[0]] * 5,
        "irregular, 8 sites, degrees 1-4": None,
    }
    edges8 = [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (2, 5), (5, 6), (6, 7), (3, 7)]
    nb8 = [[] for _ in range(8)]
    for a, b in edges8:
        nb8[a].append(b)
        nb8[b].append(a)
    graphs["irregular, 8 sites, degrees 1-4"] = nb8
    for name, nb in graphs.items():
        N = len(nb)
        E2 = sum(len(x) for x in nb)            # 2|E|
        for comp in [(1, 1), (2, 0), (2, 1), (3, 0), (2, 2), (3, 1), (4, 0)]:
            n = sum(comp)
            B = list(basis(N, *comp))
            mu2 = Fraction(sum(h2_diag(a, nb) for a in B), len(B))
            check("sec:mu2theorem", f"mu2 {name} {comp}", mu2, Fraction(E2 * n * (N - n), N * (N - 1)))

    # app:mu4fpc#validation: the finite-population mu4 against brute force, random population
    import random
    rng = random.Random(20261112)
    raw = [rng.randint(-9, 9) for _ in range(10)]
    pop = [Fraction(x) - Fraction(sum(raw), len(raw)) for x in raw]      # centred
    for k in (2, 3, 4):
        sums = [sum(c) for c in combinations(pop, k)]
        brute = (sum(x ** 2 for x in sums) / len(sums), sum(x ** 4 for x in sums) / len(sums))
        check("app:mu4fpc", f"random population N=10 k={k}: brute force = formulas", brute,
              fpc_formulas(pop, k))

    # app:numerics#signrule: the sorted-tuple rule against an independent Jordan-Wigner
    # implementation on bit strings, and H_inf Hermitian
    def jw_hop(mask, s, t):
        """c_t^dag c_s on the occupation bit string mask; returns (new mask, sign)."""
        sign = -1 if bin(mask & ((1 << s) - 1)).count("1") % 2 else 1
        mask ^= 1 << s
        sign *= -1 if bin(mask & ((1 << t) - 1)).count("1") % 2 else 1
        return mask | (1 << t), sign
    rng = random.Random(4000)
    mismatches = 0
    for _ in range(4000):
        Nsites = 12
        k = rng.randint(1, 8)
        occ = sorted(rng.sample(range(Nsites), k))
        s_from = rng.choice(occ)
        s_to = rng.choice([x for x in range(Nsites) if x not in occ])
        new_t, sign = st.hop_ktuple(tuple(occ), s_from, s_to)
        mask = sum(1 << x for x in occ)
        new_mask, jw_sign = jw_hop(mask, s_from, s_to)
        if sum(1 << x for x in new_t) != new_mask or sign != jw_sign:
            mismatches += 1
    check("app:numerics", "sign rule vs Jordan-Wigner, 4000 random moves", mismatches, 0)
    for (L, nup, ndn) in [(3, 2, 1), (4, 2, 2), (4, 3, 1)]:
        H, _ = build_Uinf_H_sparse(L, nup, ndn, lam=1.0)
        check("app:numerics", f"H_inf symmetric L={L} ({nup},{ndn})", abs(H - H.T).max(), 0)

    # sec:discussion#bond-linearity: with bond-dependent (complex, Hermitian, spin-independent)
    # amplitudes mu4(U=inf) stays exactly affine in P_same at fixed (N,n); only the slope changes.
    # Independent construction: Jordan-Wigner on 2N spin-orbitals (up block, then down block),
    # Gaussian-integer amplitudes, exact integer traces. Random graph, N=8, n=4.
    import numpy as np
    grng = random.Random(14)
    Ng = 8
    gedges = sorted({tuple(sorted(grng.sample(range(Ng), 2))) for _ in range(16)})
    amp = {e: complex(grng.choice([1, 2, 3]), grng.choice([-2, -1, 0, 1, 2])) for e in gedges}

    def mu4_weighted(nup, ndn, amps):
        states = []
        for up in combinations(range(Ng), nup):
            for dn in combinations([x for x in range(Ng) if x not in up], ndn):
                states.append(sum(1 << x for x in up) | sum(1 << (Ng + x) for x in dn))
        index = {m: i for i, m in enumerate(states)}
        D = len(states)
        Hr = np.zeros((D, D), dtype=np.int64)
        Hi = np.zeros((D, D), dtype=np.int64)
        for a, m in enumerate(states):
            for (i, j), t in amps.items():
                for (src, dst, tt) in ((j, i, t), (i, j, t.conjugate())):   # -t_ij c_i^dag c_j + h.c.
                    if (m >> dst) & 1 or (m >> (Ng + dst)) & 1:
                        continue                                           # P_0: target must be empty
                    for off in (0, Ng):
                        if (m >> (off + src)) & 1:
                            m2, sg = jw_hop(m, off + src, off + dst)
                            b = index[m2]
                            Hr[b, a] += -sg * int(tt.real)
                            Hi[b, a] += -sg * int(tt.imag)
        assert (Hr == Hr.T).all() and (Hi == -Hi.T).all()                # Hermitian
        H2r = Hr @ Hr - Hi @ Hi
        H2i = Hr @ Hi + Hi @ Hr
        return Fraction(int((H2r * H2r).sum() + (H2i * H2i).sum()), D)

    slopes = {}
    for name, amps in (("bond-dependent", amp), ("uniform", {e: complex(1, 0) for e in gedges})):
        m40, m31, m22 = (mu4_weighted(4, 0, amps), mu4_weighted(3, 1, amps), mu4_weighted(2, 2, amps))
        slopes[name] = ((m40 - m31) / 3, (m31 - m22) / 1)              # P_same = 6, 3, 2
    check("sec:discussion#bond-linearity", "random graph N=8, n=4, complex bond amplitudes: equal slopes",
          slopes["bond-dependent"][0] == slopes["bond-dependent"][1], True)
    check("sec:discussion#bond-linearity", "same graph: the slope differs from the uniform-hopping slope",
          (slopes["uniform"][0] == slopes["uniform"][1], slopes["bond-dependent"][0] != slopes["uniform"][0]),
          (True, True))

    # app:mu4walks#cubic: alpha(27, 2) on the periodic 3x3x3 lattice, by channel
    nb3, _ = torus_neighbors((3, 3, 3))
    by_type = {"edge pairs": Fraction(0), "face-diagonal pairs": Fraction(0), "other pairs": Fraction(0)}
    for a, b in combinations(range(27), 2):
        delta = h4_diag(cfg([a, b], []), nb3) - Fraction(
            h4_diag(cfg([a], [b]), nb3) + h4_diag(cfg([b], [a]), nb3), 2)
        common = len(set(nb3[a]) & set(nb3[b]))
        key = "edge pairs" if b in nb3[a] else ("face-diagonal pairs" if common == 2 else "other pairs")
        by_type[key] += delta
    check("app:mu4walks", "alpha(27,2) simple cubic", sum(by_type.values()) / comb(27, 2),
          Fraction(-96, 13))
    check("app:mu4walks", "cubic: edge / face-diagonal / other channel", tuple(by_type.values()),
          (Fraction(-1296), Fraction(-1296), Fraction(0)))

    # app:mu4walks#mediators-208-200 and #n3plus-residual: local (H^4)_aa, L = 5 and 6
    for L in (5, 6):
        nb, idx = torus_neighbors((L, L))
        i, k, j, l = idx[(0, 0)], idx[(1, 0)], idx[(1, 1)], idx[(0, 1)]
        check("app:mu4walks", f"L={L} n=4 plaquette, mediators same/opposite spin",
              (h4_diag(cfg([i, j], [k, l]), nb), h4_diag(cfg([i, j, k], [l]), nb)), (208, 200))
        check("app:mu4walks", f"L={L} n=3 diagonal pair + mediator, opposite/same spin",
              (h4_diag(cfg([i, j], [k]), nb), h4_diag(cfg([i, j, k], []), nb)), (186, 180))
        check("app:mu4walks", f"L={L} n=3 edge pair + plaquette corner, opposite/same",
              (h4_diag(cfg([i, k], [l]), nb), h4_diag(cfg([i, k, l], []), nb)), (182, 180))

    # ---- Rows whose evidence covered only part of the claim ----

    # sec:mu4exchange#alpha2-numeric: the two channels separately, square lattice
    for L in (4, 5, 6, 7):
        nb, _ = torus_neighbors((L, L))
        N = L * L
        per = {}
        for a, b in combinations(range(N), 2):
            delta = h4_diag(cfg([a, b], []), nb) - Fraction(
                h4_diag(cfg([a], [b]), nb) + h4_diag(cfg([b], [a]), nb), 2)
            common = len(set(nb[a]) & set(nb[b]))
            kind = "edge" if b in nb[a] else ("diagonal" if common == 2 else "other")
            per.setdefault(kind, []).append(delta)
        summary = {k: (len(v), sorted(set(v))) for k, v in per.items()}
        if L == 4:
            # the L = 4 anomaly: 48 diagonal-type pairs (16 extra, via wraparound) at -8 each,
            # and the edge channel enhanced to -12 per pair
            expected = {"edge": (32, [-12]), "diagonal": (48, [-8]), "other": (40, [0])}
        else:
            expected = {"edge": (2 * N, [-8]), "diagonal": (2 * N, [-8]),
                        "other": (comb(N, 2) - 4 * N, [0])}
        check("sec:mu4exchange", f"alpha(N,2) by channel at L={L}: (pairs, value per pair)",
              summary, expected)

    # sec:SW#crossterm-numeric: L = 5, 6 as well
    for (L, nup, ndn) in [(5, 2, 2), (5, 3, 1), (6, 1, 1), (6, 2, 1)]:
        m = sw_moments(L, nup, ndn, lam=1.0)
        check("sec:SW", f"Tr(T0 V) L={L} ({nup},{ndn})", exact(m["tr_T0V"], "Tr T0 V"), 0)

    # sec:SW#L3: at L = 3 the 1/U coefficient of mu_2c(U) from full exact diagonalization
    # matches the prediction -2 Tr(T0 V)/D0
    import numpy as np
    import three_electron as te
    def mu2c_band(H, D0):
        w = np.sort(np.linalg.eigvalsh(H))[:D0]
        return w.var()
    def two_electron_H(L, U):
        A = te.adjacency_matrix(L, te.build_neighbors(L), 1.0).toarray()
        N = L * L
        I = np.eye(N)
        return np.kron(A, I) + np.kron(I, A) + U * np.diag(np.eye(N).reshape(-1))
    for (comp, build) in [((1, 1), lambda U: two_electron_H(3, U)),
                          ((2, 1), lambda U: te.build_three_electron_H(3, U)[0].toarray())]:
        m = sw_moments(3, *comp, lam=1.0)
        D0 = m["D0"]
        c1 = -2 * m["tr_T0V"] / D0
        mu2inf = m["mu2_inf"]
        # Richardson extrapolation of U (mu2c(U) - mu2(inf)) to U -> infinity
        g = {U: U * (mu2c_band(build(U), D0) - mu2inf) for U in (400.0, 800.0)}
        c1_ed = 2 * g[800.0] - g[400.0]
        check("sec:SW", f"L=3 {comp}: 1/U coefficient ED vs -2Tr(T0V)/D0 (rel. dev < 1e-3)",
              abs(c1_ed - c1) / abs(c1) < 1e-3, True)

    # tab:fpcexact#ED: the free-fermion values against exact diagonalization
    for (k, m2, m4) in [(2, Fraction(112, 15), Fraction(2176, 15)),
                        (3, Fraction(52, 5), Fraction(9976, 35)),
                        (4, Fraction(64, 5), Fraction(197632, 455))]:
        H, _ = build_Uinf_H_sparse(4, k, 0, lam=1.0)
        w = np.linalg.eigvalsh(H.toarray())
        # relative: mu_4 is ~10^2, so an absolute 1e-12 is only ~10 ulps and depends on the BLAS
        err = max(abs((w ** 2).mean() / float(m2) - 1), abs((w ** 4).mean() / float(m4) - 1))
        check("tab:fpcexact", f"k={k}: ED moments match the closed forms (rel. < 1e-13)", err < 1e-13, True)

    # tab:swamp: the U^-2 coefficient c2 = Var(V) + 2 Tr(T0 H3)/D0 of mu_2c(U), exact at lambda = 1
    def sw_c2(L, nup, ndn):
        m = sw_moments(L, nup, ndn, lam=1.0, third_order=True)
        D0 = m["D0"]
        var_v = Fraction(exact(m["tr_Vsq"], "Tr V^2"), D0) - Fraction(exact(m["tr_V"], "Tr V"), D0) ** 2
        return var_v, var_v + 2 * Fraction(exact(m["tr_T0H3"], "Tr T0 H3"), D0)

    swamp = {(4, 0): (0, 0), (3, 0): (0, 0),
             (2, 1): ("9.643175", Fraction(-3076, 225)),
             (3, 1): ("13.756484", Fraction(-40704, 2275)),
             (2, 2): ("18.376361", Fraction(-487744, 20475))}
    c2_L4 = {}
    for comp, (var_printed, c2_expected) in swamp.items():
        var_v, c2 = sw_c2(4, *comp)
        c2_L4[comp] = c2
        got_var = var_v if var_printed == 0 else f"{float(var_v):.6f}"
        check("tab:swamp", f"L=4 {comp}: Var(V), c2", (got_var, c2), (var_printed, c2_expected))

    # sec:SW#centralmoment: c2 against full exact diagonalization of the Hubbard model at L = 4
    # (Richardson extrapolation of U^2 (mu_2c(U) - mu_2(inf)) from U = 400, 800)
    def band_var(H, D0):
        return np.sort(np.linalg.eigvalsh(H))[:D0].var()
    for comp, build in [((1, 1), lambda U: two_electron_H(4, U)),
                        ((2, 1), lambda U: te.build_three_electron_H(4, U)[0].toarray())]:
        m = sw_moments(4, *comp, lam=1.0)
        g = {U: U ** 2 * (band_var(build(U), m["D0"]) - m["mu2_inf"]) for U in (400.0, 800.0)}
        c2_ed = 2 * g[800.0] - g[400.0]
        c2 = c2_L4[comp] if comp in c2_L4 else sw_c2(4, *comp)[1]
        check("sec:SW", f"L=4 {comp}: ED U^-2 coefficient vs c2 = {float(c2):.4f} (rel. dev < 1e-3)",
              abs(c2_ed - float(c2)) / abs(float(c2)) < 1e-3, True)

    # sec:SW: c2 at L = 5 (1,1) against full exact diagonalization, and the n = 2 values
    # c2(1,1) = -96/(N-1) - 64/(N-1)^2 at L = 5..8 (computed, not derived)
    m5 = sw_moments(5, 1, 1, lam=1.0)
    g5 = {U: U ** 2 * (band_var(two_electron_H(5, U), m5["D0"]) - m5["mu2_inf"]) for U in (400.0, 800.0)}
    c2_5 = sw_c2(5, 1, 1)[1]
    check("sec:SW", f"L=5 (1,1): ED U^-2 coefficient vs c2 = {c2_5} (rel. dev < 1e-3)",
          abs(2 * g5[800.0] - g5[400.0] - float(c2_5)) / abs(float(c2_5)) < 1e-3, True)
    check("sec:SW", "c2(1,1) = -96/(N-1) - 64/(N-1)^2 at L = 5, 6, 7, 8",
          {sw_c2(L, 1, 1)[1] == Fraction(-96, L * L - 1) - Fraction(64, (L * L - 1) ** 2) for L in (5, 6, 7, 8)},
          {True})
    # sec:SW#c2-sign: c2 > 0 near half filling (L = 4, n = 14)
    check("sec:SW", "L=4 c2 near half filling: (13,1), (12,2)", (sw_c2(4, 13, 1)[1], sw_c2(4, 12, 2)[1]),
          (Fraction(6848, 1575), Fraction(23424, 2275)))

    # sec:SW#beta-trend: composition dependence of c2/(N_up N_down). Relative spread of two values
    # x, y as printed in the paper: |x - y| / mean(|x|, |y|), in percent.
    def spread(x, y):
        return f"{float(abs(x - y) / ((abs(x) + abs(y)) / 2)) * 100:.2f}"
    for L, printed in [(4, BETA_SPREAD[4]), (5, BETA_SPREAD[5]), (6, BETA_SPREAD[6])]:
        b31, b22 = sw_c2(L, 3, 1)[1] / 3, sw_c2(L, 2, 2)[1] / 4
        check("sec:SW#beta", f"L={L} n=4: c2/(N_up N_down), (3,1) vs (2,2), relative spread %",
              spread(b31, b22), printed)
    b41, b32 = sw_c2(4, 4, 1)[1] / 4, sw_c2(4, 3, 2)[1] / 6
    check("sec:SW#beta", "L=4 n=5: c2/(N_up N_down), (4,1) vs (3,2), relative spread %",
          spread(b41, b32), "0.34")
    b51, b33 = sw_c2(4, 5, 1)[1] / 5, sw_c2(4, 3, 3)[1] / 9
    check("sec:SW#beta", "L=4 n=6: c2/(N_up N_down), (5,1) vs (3,3), relative spread %",
          spread(b51, b33), "0.79")
    check("sec:SW#c2-sign", "L=4 n=6: c2 < 0 for (5,1), (3,3)", (b51 < 0, b33 < 0), (True, True))

    # sec:mu4exchange#alphaN: alpha(N, n) = -8 (N-n)(8N-11n-2) / [(N-1)(N-2)(N-3)] against exact
    # slopes in P_same (every pair of adjacent compositions) on L x L tori with L = 3 or L >= 5
    def alpha_formula(N, n):
        return Fraction(-8 * (N - n) * (8 * N - 11 * n - 2), (N - 1) * (N - 2) * (N - 3))

    def p_same(a, b):
        return comb(a, 2) + comb(b, 2)
    for L, n in [(3, 3), (3, 4), (3, 5), (5, 3), (5, 4), (6, 3), (7, 3)]:
        comps = [(n - k, k) for k in range(n // 2 + 1)]
        mu4 = {c: uinf_moments(L, *c)[1] for c in comps}
        slopes = {(mu4[c] - mu4[d]) / (p_same(*c) - p_same(*d)) for c, d in zip(comps, comps[1:])}
        check("sec:mu4exchange", f"alpha(N,n) closed form, L={L} n={n} (all slopes)", slopes,
              {alpha_formula(L * L, n)})
        nbL = torus_neighbors((L, L))[0]
        check("eq:Aclosed", f"mu4 = A + alpha P_same, L={L} n={n}, every composition",
              mu4, {c: m4c.mu4_fermion(nbL, *c) for c in comps})
    check("sec:mu4exchange", "alpha(25,6) closed form = n=6 evidence slope -38/23",
          alpha_formula(25, 6), Fraction(-38, 23))
    # eq:alphaC4: on any finite simple graph, alpha(N,n) = -8 C4 (N-n)(8N-11n-2) / [N(N-1)(N-2)(N-3)]
    def alpha_c4(N, n, C):
        return Fraction(-8 * C * (N - n) * (8 * N - 11 * n - 2), N * (N - 1) * (N - 2) * (N - 3))

    def mu4_graph(nb, a, b):
        B = list(basis(len(nb), a, b))
        return Fraction(sum(h4_diag(x, nb) for x in B), len(B))
    graphs = dict(small_graphs(), **{"torus 4x4": torus_neighbors((4, 4))[0]})
    for name, nb in graphs.items():
        N, C = len(nb), four_cycles(nb)
        for n in (2, 3, 4):
            comps = [(n - k, k) for k in range(n // 2 + 1)]
            m = {c: mu4_graph(nb, *c) for c in comps}
            slopes = {(m[c] - m[d]) / (p_same(*c) - p_same(*d)) for c, d in zip(comps, comps[1:])}
            check("sec:mu4exchange", f"alpha(N,n) = C4 form on {name} (N={N}, C4={C}), n={n}", slopes,
                  {alpha_c4(N, n, C)})
            check("eq:Aclosed", f"mu4 = A + alpha P_same on {name}, n={n}, every composition",
                  m, {c: m4c.mu4_fermion(nb, *c) for c in comps})
    check("sec:mu4exchange", "alpha(N,2) closed form reduces to -64/(N-1)",
          {alpha_formula(N, 2) == Fraction(-64, N - 1) for N in range(9, 200)}, {True})

    # app:mu4walks#hcb-lemma: mu4 of n hard-core bosons (the n-token graph) is
    # (2m + 4W + 8C4) p11 + (24D + 16C4) p22, against exact enumeration in every sector
    hcb_graphs = dict(small_graphs(), **{"torus 4x4": torus_neighbors((4, 4))[0],
                                         "torus 3x4": torus_neighbors((3, 4))[0],
                                         "kagome 2x2 (N=12)": kagome_neighbors(2)})
    for name, nb in hcb_graphs.items():
        ns = [n for n in range(len(nb) + 1) if comb(len(nb), n) <= 5000]
        check("app:mu4walks#hcb-lemma", f"mu4_HCB closed form on {name}, n = 0..{ns[-1]}",
              [m4c.hcb_mu4_exact(nb, n) for n in ns], [m4c.mu4_hcb(nb, n) for n in ns])
    # eq:Aclosed: the values printed in tab:mu4exact (L = 4) and tab:n6test (L = 5, n = 6)
    printed = {(4, 2, 0): Fraction(2176, 15), (4, 1, 1): Fraction(2272, 15), (4, 3, 0): Fraction(9976, 35),
               (4, 2, 1): Fraction(10348, 35), (4, 4, 0): Fraction(197632, 455),
               (4, 3, 1): Fraction(203536, 455), (4, 2, 2): Fraction(15808, 35),
               (5, 6, 0): Fraction(253593, 253), (5, 5, 1): Fraction(255683, 253),
               (5, 4, 2): Fraction(256937, 253), (5, 3, 3): Fraction(257355, 253)}
    check("eq:Aclosed", "A + alpha P_same = every value printed in tab:mu4exact, tab:n6test",
          {k: m4c.mu4_fermion(torus_neighbors((k[0], k[0]))[0], k[1], k[2]) for k in printed}, printed)
    check("eq:Aclosed", "A(16, n) at L=4 for n = 2, 3, 4",
          tuple(m4c.intercept(torus_neighbors((4, 4))[0], n) for n in (2, 3, 4)),
          (Fraction(2272, 15), Fraction(10534, 35), Fraction(5984, 13)))
    # sec:mu4exchange#xy-limit: the grand-canonical limit p_ab -> rho^a (1 - rho)^b gives
    # kappa4/N = (2m+4W+8C4)/N q - (12m+24W-16C4)/N q^2 (q = rho(1-rho)); on the f.c.c. lattice
    # this is the K^4 coefficient 12{x^2 y + 22 x^3 (y + y^2) + 22 x^4 (y + y^3) - 50 x^4 y^2}
    # = 540 q - 1128 q^2 of Rogiers & Dekeyser, Phys. Lett. A 46, 206 (1973)
    Nf, mf, Wf, C4f, _ = m4c.invariants(m4c.fcc_neighbors(3))
    check("sec:mu4exchange#xy-limit", "f.c.c.: (m, W, C4)/N and the q, q^2 coefficients of kappa4/N",
          (Fraction(mf, Nf), Fraction(Wf, Nf), Fraction(C4f, Nf),
           Fraction(2 * mf + 4 * Wf + 8 * C4f, Nf), Fraction(-(12 * mf + 24 * Wf - 16 * C4f), Nf)),
          (6, 66, 33, 540, -1128))

    # app:mu4walks#hypercubic: alpha_d(N,2) = -16(d-1)z/(N-1) on tori with every side 3 or >= 5;
    # it fails as soon as one side is 4
    def alpha2_pairs(shape):
        nb, _ = torus_neighbors(shape)
        N = len(nb)
        tot = Fraction(0)
        for a, b in combinations(range(N), 2):
            tot += h4_diag(cfg([a, b], []), nb) - Fraction(
                h4_diag(cfg([a], [b]), nb) + h4_diag(cfg([b], [a]), nb), 2)
        return tot / comb(N, 2), N
    for shape, printed in [((5, 5, 5), Fraction(-48, 31)), ((4, 4, 4), Fraction(-80, 21)),
                           ((3, 4), Fraction(-80, 11)), ((4, 5), Fraction(-80, 19))]:
        d, m = len(shape), sum(1 for side in shape if side == 4)
        a2, N = alpha2_pairs(shape)
        # sides of length 4 add axis-ring 4-cycles: alpha = -16 [2d(d-1) + m] / (N-1)
        check("app:mu4walks", f"alpha(N,2) on {'x'.join(map(str, shape))} (m={m} sides of 4): value, formula",
              (a2, a2 == Fraction(-16 * (2 * d * (d - 1) + m), N - 1)), (printed, True))
    # app:mu4walks#nonclaim-graphgeneral: kagome (d = 2, z = 4 like the square lattice) has alpha(N,2) = 0
    for Lk in (3, 4):
        nbk = kagome_neighbors(Lk)
        Nk = len(nbk)
        tot = sum(h4_diag(cfg([a, b], []), nbk) - Fraction(h4_diag(cfg([a], [b]), nbk) + h4_diag(cfg([b], [a]), nbk), 2)
                  for a, b in combinations(range(Nk), 2))
        check("app:mu4walks", f"kagome N={Nk}: alpha(N,2)", tot / comb(Nk, 2), 0)

    # sec:futurework#alphaflux: alpha(N,2,Phi) = -64/(N-1) cos Phi at quantized uniform flux
    # Phi = 2 pi p / N, on L = 5 and 6 (and not at L = 4, where it fails already at Phi = 0)
    import mu4_flux_validation as mfv
    for L, step in [(3, 1), (5, 1), (6, 1), (7, 3)]:
        N = L * L
        worst, worst_orb = 0.0, 0.0
        mu4_11_0 = None
        for p in range(0, N, step):
            alpha_link = 2 * np.pi * p / N
            H20, D20 = mfv.build_H(L, 2, 0, 1.0, alpha_link)
            H11, D11 = mfv.build_H(L, 1, 1, 1.0, alpha_link)
            m11 = mfv.mu2_mu4_sparse(H11, D11)[1]
            mu4_11_0 = m11 if p == 0 else mu4_11_0
            D = mfv.mu2_mu4_sparse(H20, D20)[1] - m11
            worst = max(worst, abs(D + 64 / (N - 1) * np.cos(alpha_link)))
            # orbital (spin-blind) plaquette-loop piece: mu4^(1,1)(Phi) - mu4^(1,1)(0)
            worst_orb = max(worst_orb, abs(m11 - mu4_11_0 - 16 * (N - 4) * (np.cos(alpha_link) - 1) / (N - 1)))
        which = "all" if step == 1 else f"every {step}rd of the"
        check("sec:futurework", f"alpha(N,2,Phi) = -64/(N-1) cos Phi, {which} {N} fluxes, L={L} (< 1e-12)",
              worst < 1e-12, True)
        check("sec:futurework", f"orbital mu4^(1,1)(Phi)-mu4^(1,1)(0) = 16(N-4)(cos Phi-1)/(N-1), L={L}",
              worst_orb < 1e-12, True)

    # eq:mu4flux: mu4 under arbitrary Peierls phases, on any finite simple graph with N >= 4:
    # mu4 = (2m + 4W) p11 + 24 D p22 + B(N, n, P_same) sum_C cos Theta_C (Theta_C the Wilson phase of
    # the 4-cycle C). H_inf is built from fermion operators by checks/hinf_flux.py, independently of
    # mu4_flux_validation.py, except where the manuscript's own gauge is the point (L = 4 below).
    import hinf_flux as hf
    check("eq:mu4flux", "B(N,n,P_same) = walk-count form of App. C, N=4..40",
          {m4c.flux_coefficient(N, a, n - a) == m4c.flux_coefficient_walks(N, a, n - a)
           for N in range(4, 41) for n in range(N + 1) for a in range(n + 1)}, {True})
    rng = np.random.default_rng(2026)

    def random_graph(N, prob):
        edges = [(u, w) for u, w in combinations(range(N), 2) if rng.random() < prob]
        return [sorted({w for u, w in edges if u == v} | {u for u, w in edges if w == v}) for v in range(N)]
    flux_graphs = [(f"random N={N} #{k}", random_graph(N, prob)) for k, (N, prob) in
                   enumerate([(4, 0.8), (5, 0.6), (5, 0.9), (6, 0.5), (6, 0.7), (7, 0.5), (7, 0.6)])]
    flux_graphs += [("K6", small_graphs()["K6"]), ("triangular 3x3", small_graphs()["triangular 3x3"])]
    worst, exact_ok, n_exact, n_float = 0.0, True, 0, 0
    for name, nb in flux_graphs:
        N, inv, cycles = len(nb), m4c.invariants(nb), m4c.four_cycle_list(nb)
        quarter = {(u, w): int(rng.integers(4)) for u in range(N) for w in nb[u] if u < w}
        real = {(u, w): rng.uniform(-np.pi, np.pi) for u in range(N) for w in nb[u] if u < w}

        def ph_q(x, y):
            return (np.pi / 2) * (quarter[(x, y)] if x < y else -quarter[(y, x)])

        def ph_r(x, y):
            return real[(x, y)] if x < y else -real[(y, x)]
        # exact: phases multiple of pi/2, so H has entries in {±1, ±i}, Tr H^4 is an integer and
        # sum_C cos Theta_C is an integer
        cos_q = sum(round(np.cos(ph_q(a, b) + ph_q(b, c) + ph_q(c, d) + ph_q(d, a))) for a, b, c, d in cycles)
        cos_r = hf.wilson_cos_sum(cycles, ph_r)
        for n in range(N + 1):
            for a in range(n + 1):
                b = n - a
                if len(hf.basis(N, a, b)) > 1500:
                    continue
                Hq, Bq = hf.build(nb, a, b, ph_q)
                exact_ok &= Fraction(hf.tr4_exact(Hq), len(Bq)) == m4c.mu4_fermion_flux(nb, a, b, cos_q, inv)
                Hr, Br = hf.build(nb, a, b, ph_r)
                worst = max(worst, abs(hf.mu4(Hr, len(Br)) - float(m4c.flux_baseline(nb, n, inv))
                                       - float(m4c.flux_coefficient(N, a, b)) * cos_r))
                n_exact += 1
                n_float += 1
    check("eq:mu4flux", f"exact, phases in (pi/2)Z: {n_exact} sectors, {len(flux_graphs)} graphs", exact_ok, True)
    check("eq:mu4flux", f"random phases: {n_float} sectors, max deviation < 1e-12", worst < 1e-12, True)
    # sec:futurework#L4-winding: on the 4x4 torus, in the manuscript's Landau gauge
    # (mu4_flux_validation.link_phase), the 24 four-cycles are the 16 plaquettes (Theta = Phi) and the
    # 4 rows and 4 columns, which wind around the torus: Theta = 4 Phi y and -4 Phi x, so
    # sum_C cos Theta_C = 16 cos Phi + 2 sum_{k=0..3} cos(4 k Phi) = 16 cos Phi + 2 + 4 cos 4Phi + 2 cos 8Phi
    # at the quantized fluxes Phi = 2 pi p / 16. With boundary twists th_x, th_y on the wrap-around
    # bonds the rows and columns carry 4 Phi y + th_x and th_y - 4 Phi x instead.
    nb4 = torus_neighbors((4, 4))[0]
    cyc4, inv4 = m4c.four_cycle_list(nb4), m4c.invariants(nb4)

    def site(v):
        return v // 4, v % 4   # torus_neighbors((4, 4)) numbers (x, y) as 4 x + y

    def gauge(al, thx=0.0, thy=0.0):
        def ph(u, w):
            (x, y), (x2, y2) = site(u), site(w)
            dx, dy = (x2 - x + 1) % 4 - 1, (y2 - y + 1) % 4 - 1
            twist = (thx if (dx == 1 and x == 3) else -thx if (dx == -1 and x == 0) else 0.0) + \
                (thy if (dy == 1 and y == 3) else -thy if (dy == -1 and y == 0) else 0.0)
            return mfv.link_phase(x, y, dx, dy, 4, al) + twist
        return ph
    ok_sum, ok_mfv, ok_twist = True, 0.0, 0.0
    for pq in range(16):
        al = 2 * np.pi * pq / 16
        s = hf.wilson_cos_sum(cyc4, gauge(al))
        ok_sum &= abs(s - (16 * np.cos(al) + 2 + 4 * np.cos(4 * al) + 2 * np.cos(8 * al))) < 1e-12
        for a, b in [(2, 0), (1, 1), (2, 1)]:
            H, D = mfv.build_H(4, a, b, 1.0, al)
            ok_mfv = max(ok_mfv, abs(mfv.mu2_mu4_sparse(H, D)[1] -
                                     float(m4c.mu4_fermion_flux(nb4, a, b, Fraction(0), inv4)) -
                                     float(m4c.flux_coefficient(16, a, b)) * s))
    check("sec:futurework", "L=4: sum_C cos = 16cos P + 2 + 4cos 4P + 2cos 8P, 16 fluxes", ok_sum, True)
    check("sec:futurework", "L=4: mu4(Phi) of build_H = eq:mu4flux, 16 fluxes (< 1e-12)", ok_mfv < 1e-12, True)
    for thx, thy in [(0.7, -1.9), (2.3, 0.4)]:
        for pq in (1, 3, 6):
            al = 2 * np.pi * pq / 16
            ph = gauge(al, thx, thy)
            s = hf.wilson_cos_sum(cyc4, ph)
            pred_s = 16 * np.cos(al) + sum(np.cos(4 * al * k + thx) + np.cos(thy - 4 * al * k) for k in range(4))
            for a, b in [(2, 0), (1, 1)]:
                H, B4 = hf.build(nb4, a, b, ph)
                ok_twist = max(ok_twist, abs(s - pred_s), abs(hf.mu4(H, len(B4)) -
                               float(m4c.flux_baseline(nb4, a + b, inv4)) - float(m4c.flux_coefficient(16, a, b)) * s))
    check("sec:futurework", "L=4 with twists: winding loops carry 4Phi y+th_x, th_y-4Phi x", ok_twist < 1e-12, True)
    # sec:futurework#alphaflux-n: on the L x L torus (L = 3 or L >= 5) every 4-cycle is a plaquette, so
    # mu4(Phi) = F + B N cos Phi for every composition: alpha(N, n, Phi) = alpha(N, n) cos Phi
    worst5 = 0.0
    nb5 = torus_neighbors((5, 5))[0]
    inv5 = m4c.invariants(nb5)
    for pq in (0, 2, 5, 9, 13):
        al = 2 * np.pi * pq / 25
        for a, b in [(3, 0), (2, 1)]:
            H, D = mfv.build_H(5, a, b, 1.0, al)
            worst5 = max(worst5, abs(mfv.mu2_mu4_sparse(H, D)[1] - float(m4c.flux_baseline(nb5, a + b, inv5))
                                     - float(m4c.flux_coefficient(25, a, b)) * 25 * np.cos(al)))
    check("sec:futurework", "L=5, n=3: mu4(Phi) = F + B N cos Phi, 5 fluxes (< 1e-12)", worst5 < 1e-12, True)

    # sec:futurework#twist-periodicity: the exact two-electron U-band under a boundary twist theta
    # is pi-periodic up to corrections ~ lambda^L / U^(L-1), and follows the doubled-twist
    # doublon dispersion to O(lambda^4/U^3)
    def twisted_two_electron(L, U, th):
        N = L * L
        T = np.zeros((N, N), complex)
        for x in range(L):
            for y in range(L):
                i, j, k = x * L + y, ((x + 1) % L) * L + y, x * L + (y + 1) % L
                ph = np.exp(1j * th) if x == L - 1 else 1.0
                T[j, i] -= ph
                T[i, j] -= np.conj(ph)
                T[k, i] -= 1
                T[i, k] -= 1
        H = np.kron(T, np.eye(N)) + np.kron(np.eye(N), T) + U * np.diag(np.eye(N).reshape(-1))
        return np.sort(np.linalg.eigvalsh(H))[-N:]
    L = 6
    devs, model_devs = {}, {}
    for U in (20.0, 40.0):
        K = 2 * np.pi * np.arange(L) / L
        devs[U], model_devs[U] = 0.0, 0.0
        for th in (0.1, 0.6, 1.1):
            band = twisted_two_electron(L, U, th)
            devs[U] = max(devs[U], np.abs(band - twisted_two_electron(L, U, th + np.pi)).max())
            model = np.sort((U + 8 / U + 4 / U * (np.cos(K[:, None] + 2 * th / L) + np.cos(K[None, :]))).ravel())
            model_devs[U] = max(model_devs[U], np.abs(band - model).max())
    check("sec:futurework", "L=6 twist: U-band deviation from pi-periodicity at U=20, 40",
          (f"{devs[20.0]:.0e}", f"{devs[40.0]:.0e}"), ("1e-04", "3e-06"))
    check("sec:futurework", "L=6 twist: ratio U=20/U=40 within 30% of 2^(L-1) = 32",
          abs(devs[20.0] / devs[40.0] / 32 - 1) < 0.3, True)
    for Lt in (4, 5):
        d = {U: max(np.abs(twisted_two_electron(Lt, U, th) - twisted_two_electron(Lt, U, th + np.pi)).max()
                    for th in (0.1, 0.6, 1.1)) for U in (20.0, 40.0)}
        check("sec:futurework", f"L={Lt} twist: ratio U=20/U=40 within 30% of 2^(L-1) = {2 ** (Lt - 1)}",
              abs(d[20.0] / d[40.0] / 2 ** (Lt - 1) - 1) < 0.3, True)
    # sec:benchmark#doublonH: at L = 3 a third-order term shifts the U-band centre by -8 lambda^3/U^2
    U3 = 80.0
    centre = twisted_two_electron(3, U3, 0.0).mean()
    check("sec:benchmark", "L=3 U-band centre: (centre - eps_d) U^2 within 3% of -8 at U=80",
          abs((centre - (U3 + 8 / U3)) * U3 ** 2 / -8 - 1) < 0.03, True)
    check("sec:futurework", "L=6 twist: U-band vs doubled-twist doublon model at U=20, 40",
          (f"{model_devs[20.0]:.0e}", f"{model_devs[40.0]:.0e}"), ("8e-03", "1e-03"))

    n_fail = RESULTS.count(False)
    print(f"\n{len(RESULTS) - n_fail}/{len(RESULTS)} checks passed in {time.time() - t0:.1f} s")
    return 1 if n_fail else 0


if __name__ == "__main__":
    sys.exit(main())
