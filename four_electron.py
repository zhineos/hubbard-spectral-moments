#!/usr/bin/env python3
"""
Phase 3 of the dimensional-reduction test sequence: four electrons,
N_up=2, N_down=2, on an LxL periodic lattice.

Basis: BOTH spin species are antisymmetrized pairs, built with the same
machinery as three_electron.py (reused directly): up-pair index
(i1,i2), i1<i2, and down-pair index (j1,j2), j1<j2, independently.

H = H_pp(x) I_down  +  I_up (x) H_pp(down)  +  U * N_d_indicator

Doublon occupation for basis state ((i1,i2),(j1,j2)):
    N_d = |{i1,i2} intersect {j1,j2}|   (0, 1, or 2)
this IS the interaction indicator (divided by U), same trick as before.

Hilbert dimension: D = [L^2*(L^2-1)/2]^2 -- L=4 (N=16) gives 120^2=14400.
"""

import numpy as np
from scipy.sparse import kron, identity, diags, csr_matrix

from three_electron import (
    LAM, build_neighbors, adjacency_matrix, build_pair_basis, build_H_uu,
)

OUT = "results"


def build_four_electron_H(L, U, lam=LAM):
    N = L * L
    neighbors = build_neighbors(L)
    pairs, index = build_pair_basis(N)
    H_pp = build_H_uu(L, neighbors, pairs, index, lam)   # same for either spin
    n_pairs = len(pairs)

    I_pairs = identity(n_pairs, format="csr")

    H = kron(H_pp, I_pairs) + kron(I_pairs, H_pp)

    # doublon-occupation indicator, diagonal in the (up_pair, down_pair) basis
    site_to_pairidx = {}
    for p_idx, (i, j) in enumerate(pairs):
        site_to_pairidx.setdefault(i, []).append(p_idx)
        site_to_pairidx.setdefault(j, []).append(p_idx)

    # build indicator by summing, for each site s, an outer "both contain s"
    # contribution -- do it directly and simply (n_pairs is a few hundred,
    # this is cheap) rather than cleverly
    indicator = np.zeros(n_pairs * n_pairs)
    pair_sets = [set(p) for p in pairs]
    for up_idx, up_set in enumerate(pair_sets):
        base = up_idx * n_pairs
        for down_idx, down_set in enumerate(pair_sets):
            nd = len(up_set & down_set)
            if nd:
                indicator[base + down_idx] = nd

    H = H + U * diags(indicator)
    return csr_matrix(H), indicator, pairs, index, N


def n_d_expectation(eigenvectors, indicator):
    prob = np.abs(eigenvectors) ** 2
    return indicator @ prob


if __name__ == "__main__":
    print("Module loaded.")
