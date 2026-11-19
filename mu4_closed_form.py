"""Closed form of the U = infinity fourth moment on any finite simple graph (uniform hopping, lambda = 1).

Paper labels: app:mu4walks#hcb-lemma (the hard-core-boson lemma), eq:Aclosed (the intercept A(N, n)),
eq:alphaN (the exchange slope, already in the paper) and sec:mu4exchange#proposition (the complete
fourth moment).

Graphs are neighbour lists, as in checks/hinf_local.py. With N vertices, m edges, W = sum_v C(d_v, 2)
wedges, C4 four-cycles (cycle subgraphs, chords allowed) and D = C(m, 2) - W pairs of vertex-disjoint
edges, and the canonical occupation probabilities

    p_ab = (n)_a (N - n)_b / (N)_(a+b)      ((x)_r the falling factorial),

the closed forms are

    mu4_HCB(N, n)       = (2m + 4W + 8 C4) p11 + (24 D + 16 C4) p22      (n hard-core bosons)
    A(N, n)             = mu4_HCB - T2 - (3/2) T3,   T2 = 32 C4 p22,  T3 = 8 C4 p31
                        = (2m + 4W + 8 C4) p11 + (24 D - 16 C4) p22 - 12 C4 p31
    mu4(N_up, N_down)   = A(N, n) + alpha(N, n) P_same,   P_same = C(N_up, 2) + C(N_down, 2)
    alpha(N, n)         = -8 C4 (N - n)(8N - 11n - 2) / [N (N-1)(N-2)(N-3)]

and, with Peierls phases A_ij = -A_ji on the bonds (eq:mu4flux), Theta_C the Wilson phase of the
4-cycle C (the sum of A around it) and N >= 4,

    mu4(Theta)          = (2m + 4W) p11 + 24 D p22 + B(N, n, P_same) sum_C cos Theta_C
    B(N, n, P_same)     = 8 p11 - 16 p22 - 12 p31 - 8 (N - n)(8N - 11n - 2) / [N (N-1)(N-2)(N-3)] P_same

which reduces to A + alpha P_same at Theta = 0 (sum_C 1 = C4).

All values are exact Fractions.
"""
from fractions import Fraction
from itertools import combinations
from math import comb


def falling(x, r):
    out = 1
    for k in range(r):
        out *= x - k
    return out


def p(N, n, a, b):
    """Probability that a given sites are occupied and b given other sites empty (uniform n-subset)."""
    den = falling(N, a + b)
    if den == 0:  # N < a + b: the numerator vanishes too
        return Fraction(0)
    return Fraction(falling(n, a) * falling(N - n, b), den)


def invariants(nbrs):
    """(N, m, W, C4, D) of a simple graph given as neighbour lists."""
    N = len(nbrs)
    sets = [set(x) for x in nbrs]
    m = sum(len(s) for s in sets) // 2
    W = sum(comb(len(s), 2) for s in sets)
    C4 = sum(comb(len(sets[u] & sets[w]), 2) for u, w in combinations(range(N), 2)) // 2
    return N, m, W, C4, comb(m, 2) - W


def mu2(nbrs, n, inv=None):
    N, m, *_ = inv or invariants(nbrs)
    return 2 * m * p(N, n, 1, 1)


def mu4_hcb(nbrs, n, inv=None):
    N, m, W, C4, D = inv or invariants(nbrs)
    return (2 * m + 4 * W + 8 * C4) * p(N, n, 1, 1) + (24 * D + 16 * C4) * p(N, n, 2, 2)


def intercept(nbrs, n, inv=None):
    """A(N, n): the spin-independent part of mu4(U = inf) for projected spin-1/2 fermions."""
    N, m, W, C4, D = inv or invariants(nbrs)
    return ((2 * m + 4 * W + 8 * C4) * p(N, n, 1, 1) + (24 * D - 16 * C4) * p(N, n, 2, 2)
            - 12 * C4 * p(N, n, 3, 1))


def alpha(nbrs, n, inv=None):
    N, m, W, C4, D = inv or invariants(nbrs)
    if N < 4:
        return Fraction(0)
    return Fraction(-8 * C4 * (N - n) * (8 * N - 11 * n - 2), N * (N - 1) * (N - 2) * (N - 3))


def mu4_fermion(nbrs, nup, ndn, inv=None):
    """mu4(U = inf) of projected spin-1/2 fermions in the sector (nup, ndn). Pass inv = invariants(nbrs)
    to avoid recomputing the graph invariants in loops."""
    n = nup + ndn
    inv = inv or invariants(nbrs)
    return intercept(nbrs, n, inv) + alpha(nbrs, n, inv) * (comb(nup, 2) + comb(ndn, 2))



def four_cycle_list(nbrs):
    """The 4-cycles of a simple graph (cycle subgraphs, chords allowed), each exactly once, as corner
    tuples (a, b, c, d) in cyclic order: a is the smallest corner, b < d its two cycle neighbours."""
    sets = [set(x) for x in nbrs]
    out = []
    for a in range(len(nbrs)):
        for b, d in combinations(sorted(v for v in sets[a] if v > a), 2):
            for c in sets[b] & sets[d]:
                if c > a:
                    out.append((a, b, c, d))
    return out


def flux_coefficient(N, nup, ndn):
    """B(N, n, P_same): the coefficient of sum_C cos Theta_C in mu4 (eq:mu4flux), N >= 4."""
    n = nup + ndn
    psame = comb(nup, 2) + comb(ndn, 2)
    return (8 * p(N, n, 1, 1) - 16 * p(N, n, 2, 2) - 12 * p(N, n, 3, 1)
            - Fraction(8 * (N - n) * (8 * N - 11 * n - 2), N * (N - 1) * (N - 2) * (N - 3)) * psame)


def flux_coefficient_walks(N, nup, ndn):
    """The same coefficient as counted in the proof (App. C), before the two-species identities:
    8 p13 - 32 s2 p22 + 8 s3 p31, with s2 = P_same/C(n,2) and s3 = P3/C(n,3) the probabilities that
    two (three) given occupied sites carry equal spins; written without dividing by C(n,2), C(n,3)."""
    n = nup + ndn
    psame = comb(nup, 2) + comb(ndn, 2)
    p3 = comb(nup, 3) + comb(ndn, 3)
    d4 = falling(N, 4)
    return (8 * p(N, n, 1, 3) - Fraction(64 * psame * (N - n) * (N - n - 1), d4)
            + Fraction(48 * p3 * (N - n), d4))


def flux_baseline(nbrs, n, inv=None):
    """The flux-independent part of mu4: (2m + 4W) p11 + 24 D p22, the same for every spin composition."""
    N, m, W, C4, D = inv or invariants(nbrs)
    return (2 * m + 4 * W) * p(N, n, 1, 1) + 24 * D * p(N, n, 2, 2)


def mu4_fermion_flux(nbrs, nup, ndn, cos_sum, inv=None):
    """mu4 of projected spin-1/2 fermions with Peierls phases, given cos_sum = sum_C cos Theta_C over the
    4-cycles (exact if cos_sum is a Fraction or an int)."""
    inv = inv or invariants(nbrs)
    return flux_baseline(nbrs, nup + ndn, inv) + flux_coefficient(inv[0], nup, ndn) * cos_sum


def hcb_parts(nbrs, n):
    """The three contributions to mu4_HCB, by the number of occupied sites a two-hop path changes:
    0 (cut fluctuations), 1 (one site replaced), 2 (two sites replaced)."""
    N, m, W, C4, D = invariants(nbrs)
    p11, p22 = p(N, n, 1, 1), p(N, n, 2, 2)
    return (2 * m + 2 * W) * p11 + 8 * D * p22, (2 * W + 8 * C4) * p11, 16 * (D + C4) * p22


def hcb_mu4_exact(nbrs, n):
    """Exact mu4 of n hard-core bosons (the adjacency matrix of the n-token graph), by enumeration:
    Tr H^4 = sum_{S, S''} [(H^2)_{S S''}]^2, with H real symmetric. For small graphs only."""
    N = len(nbrs)
    E = [(u, w) for u in range(N) for w in nbrs[u] if u < w]
    basis = [sum(1 << i for i in c) for c in combinations(range(N), n)]
    if not basis:
        return Fraction(0)

    def hops(s):
        for u, w in E:
            if ((s >> u) & 1) != ((s >> w) & 1):
                yield s ^ (1 << u) ^ (1 << w)
    tr4 = 0
    for s in basis:
        two = {}
        for s1 in hops(s):
            for s2 in hops(s1):
                two[s2] = two.get(s2, 0) + 1
        tr4 += sum(v * v for v in two.values())
    return Fraction(tr4, len(basis))


def fcc_neighbors(L):
    """Face-centred cubic lattice: integer points with even coordinate sum, periodic cube of side 2L."""
    from itertools import product
    S = 2 * L
    sites = [s for s in product(range(S), repeat=3) if sum(s) % 2 == 0]
    idx = {s: k for k, s in enumerate(sites)}
    vecs = [v for v in product((-1, 0, 1), repeat=3) if sorted(map(abs, v)) == [0, 1, 1]]
    return [sorted({idx[tuple((a + b) % S for a, b in zip(s, v))] for v in vecs}) for s in sites]
