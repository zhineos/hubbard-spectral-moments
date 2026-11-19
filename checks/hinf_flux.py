"""H_inf = P0 H_t P0 with Peierls phases on any graph, built from fermion operators.

Written independently of mu4_flux_validation.py (whose sorted-tuple code is specific to the
L x L torus) and of hinf_local.py (real amplitudes only), for the checks of eq:mu4flux.

The orbitals are (site, spin), spin 0 = up and 1 = down, numbered o = spin * N + site; a basis
state is the bit mask of its occupied orbitals, |S> = c†_{o1} ... c†_{ok} |0> with o1 < ... < ok.
A hop of spin s from site x to an adjacent empty site y is the term
-lambda e^{i phase(x, y)} c†_{(y,s)} c_{(x,s)} of H_t, with lambda = 1, so its matrix element is
-e^{i phase(x, y)} (-1)^(orbitals of S below (x,s)) (-1)^(orbitals of S - (x,s) below (y,s)).
`phase(x, y)` is the Peierls phase of the hop x -> y and must satisfy phase(y, x) = -phase(x, y);
P0 drops every hop onto an occupied site (of either spin).
"""
from itertools import combinations

import numpy as np
from scipy.sparse import coo_matrix


def basis(N, nup, ndn):
    """The N_d = 0 configurations with nup up and ndn down particles, as orbital bit masks."""
    out = []
    for up in combinations(range(N), nup):
        rest = [v for v in range(N) if v not in up]
        for dn in combinations(rest, ndn):
            out.append(sum(1 << v for v in up) + sum(1 << (N + v) for v in dn))
    return out


def below(mask, o):
    """Number of occupied orbitals of `mask` numbered below o."""
    return bin(mask & ((1 << o) - 1)).count("1")


def build(nbrs, nup, ndn, phase):
    """The sparse matrix of H_inf on basis(N, nup, ndn) and that basis."""
    N = len(nbrs)
    B = basis(N, nup, ndn)
    index = {s: k for k, s in enumerate(B)}
    rows, cols, vals = [], [], []
    for k, S in enumerate(B):
        occupied = (S | (S >> N)) & ((1 << N) - 1)
        for spin in (0, 1):
            for x in range(N):
                o = spin * N + x
                if not (S >> o) & 1:
                    continue
                S1 = S & ~(1 << o)
                for y in nbrs[x]:
                    if (occupied >> y) & 1:
                        continue
                    o2 = spin * N + y
                    sign = (-1) ** (below(S, o) + below(S1, o2))
                    rows.append(index[S1 | (1 << o2)])
                    cols.append(k)
                    vals.append(-sign * np.exp(1j * phase(x, y)))
    n = len(B)
    return coo_matrix((vals, (rows, cols)), shape=(n, n)).tocsr(), B


def mu4(H, D):
    """Tr(H^4)/D for Hermitian H: the sum of |(H^2)_ab|^2 over all a, b, divided by D."""
    H2 = (H @ H).tocsr()
    return float((np.abs(H2.data) ** 2).sum()) / D


def tr4_exact(H):
    """Tr(H^4) as an int when every entry of H is in {±1, ±i} (phases multiple of pi/2)."""
    H2 = (H @ H).tocsr()
    t = float((np.abs(H2.data) ** 2).sum())
    r = round(t)
    if abs(t - r) > 1e-6:
        raise ValueError(f"Tr(H^4) = {t!r} is not an integer")
    return r


def wilson_cos_sum(cycles, phase):
    """sum over 4-cycles (a, b, c, d) of cos(phase(a,b) + phase(b,c) + phase(c,d) + phase(d,a))."""
    return sum(np.cos(phase(a, b) + phase(b, c) + phase(c, d) + phase(d, a)) for a, b, c, d in cycles)
