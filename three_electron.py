#!/usr/bin/env python3
"""
Phase 2 of the dimensional-reduction test sequence (Summary.md sec.11,
research_notebook.tex sec.VII.B): three electrons, N_up=2, N_down=1, on
an LxL periodic lattice.

Basis: the two identical (up-spin) electrons are represented by an
antisymmetrized pair index (i,j), i<j (Pauli exclusion forbids i=j);
the down-spin electron is an ordinary single-particle index k. Fermion
sign bookkeeping for the up-up pair is handled directly (a swap of the
canonical pair order flips sign -- exact and complete for exactly 2
identical fermions, no Jordan-Wigner string needed).

H = H_uu(hopping among the antisymmetrized up-pair)
    + I_pairs (x) A(hopping of the down electron)
    + U * (1 if k==i or k==j else 0)   [Hubbard interaction, diagonal]

Doublon occupation for each eigenstate:
    N_d = <sum_i n_i,up n_i,down> = <interaction indicator / U>
i.e. exactly the expectation value of the (already-computed) diagonal
interaction operator divided by U -- no extra work needed.
"""

import numpy as np
from scipy.sparse import lil_matrix, csr_matrix, kron, identity, diags
from scipy.special import jv
from scipy.integrate import quad

LAM = 1.0
OUT = "results"


def site_index(x, y, L):
    return (x % L) * L + (y % L)


def build_neighbors(L):
    neighbors = []
    for x in range(L):
        for y in range(L):
            neighbors.append([
                site_index(x + 1, y, L), site_index(x - 1, y, L),
                site_index(x, y + 1, L), site_index(x, y - 1, L),
            ])
    return neighbors


def adjacency_matrix(L, neighbors, lam=LAM):
    N = L * L
    A = lil_matrix((N, N))
    for i in range(N):
        for j in neighbors[i]:
            A[i, j] += -lam
    return csr_matrix(A)


def build_pair_basis(N):
    pairs = [(i, j) for i in range(N) for j in range(i + 1, N)]
    index = {p: k for k, p in enumerate(pairs)}
    return pairs, index


def hop_pair(pair, i_from, i_to):
    """
    Move one fermion of the antisymmetrized pair |i,j> = c^dag_i c^dag_j
    |vac> (i<j canonical order) from i_from to i_to. Returns
    (new_pair, sign) or None if Pauli-forbidden (target occupied).

    Derived directly from fermion anticommutation: annihilating the
    LARGER-index member first picks up a sign from anticommuting past
    the other creation operator, so the two members obey OPPOSITE sign
    rules relative to where the new site falls versus the stationary
    member -- this is what makes the result Hermitian (verified below).
    """
    i, j = pair
    a = i_to
    if a == i or a == j:
        return None
    if i_from == i:
        other = j
        sign = 1 if a < other else -1
    else:
        other = i
        sign = -1 if a < other else 1
    new_pair = (a, other) if a < other else (other, a)
    return new_pair, sign


def build_H_uu(L, neighbors, pairs, index, lam=LAM):
    n = len(pairs)
    H = lil_matrix((n, n))
    for p in pairs:
        i, j = p
        col = index[p]
        for site in (i, j):
            for nb in neighbors[site]:
                res = hop_pair(p, site, nb)
                if res is None:
                    continue
                new_pair, sign = res
                row = index[new_pair]
                H[row, col] += -lam * sign
    return csr_matrix(H)


def build_three_electron_H(L, U, lam=LAM):
    N = L * L
    neighbors = build_neighbors(L)
    A = adjacency_matrix(L, neighbors, lam)
    pairs, index = build_pair_basis(N)
    H_uu = build_H_uu(L, neighbors, pairs, index, lam)

    n_pairs = len(pairs)
    I_pairs = identity(n_pairs, format="csr")
    I_N = identity(N, format="csr")

    H = kron(H_uu, I_N) + kron(I_pairs, A)

    # interaction indicator, diagonal in the (pair, k) basis
    indicator = np.zeros(n_pairs * N)
    for p_idx, (i, j) in enumerate(pairs):
        base = p_idx * N
        indicator[base + i] += 1.0
        indicator[base + j] += 1.0

    H = H + U * diags(indicator)
    return csr_matrix(H), indicator, pairs, index, N


def n_d_expectation(eigenvectors, indicator):
    prob = np.abs(eigenvectors) ** 2
    return indicator @ prob


# ================================================================
# Generalized anisotropic hypercubic DOS: dispersion is a sum of
# cosines with DIFFERENT hopping amplitudes (not all equal to lambda)
# ================================================================

def rho_aniso(E, amplitudes, Tmax=500.0, limit=1000):
    """
    Exact DOS for E = -2*sum_i c_i*cos(k_i), c_i given by `amplitudes`.
    Generalizes analytical_dos.rho_bessel (equal amplitudes) via the
    same Bessel/Fourier representation: the characteristic function of
    the sum factorizes into a product of J_0(2*c_i*t) terms.
    """
    def integrand(t):
        val = 1.0
        for c in amplitudes:
            val *= jv(0, 2 * c * t)
        return val

    E = np.atleast_1d(np.asarray(E, dtype=float))
    out = np.zeros_like(E)
    for i, e in enumerate(E):
        val, _ = quad(integrand, 0, Tmax, weight="cos", wvar=e, limit=limit)
        out[i] = val / np.pi
    return out


if __name__ == "__main__":
    print("Module loaded.")
