"""First-order (U -> infinity) model of one doublon plus one electron at total momentum K.

Relative coordinate j = electron - doublon, j != 0, on the L x L torus. To first order in
lambda the doublon is static; the electron hops to neighbouring sites other than the doublon's
with amplitude -lambda (no fermionic sign, since the doublon's up electron always sorts first
in the representative), and the doublon's down electron hopping onto the electron's site
swaps the two, j -> -j, with amplitude +lambda exp(-i K.j) (the -1 is the reordering of the
up pair under translation). This is P_1 H_t P_1 in the K basis of slow_bound_states.k_blocks,
up to the constant U.
"""
import numpy as np


def block(L, K, lam=1.0):
    sites = [(x, y) for x in range(L) for y in range(L) if (x, y) != (0, 0)]
    idx = {s: n for n, s in enumerate(sites)}
    H = np.zeros((len(sites), len(sites)), dtype=complex)
    for (x, y), n in idx.items():
        for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            t = ((x + dx) % L, (y + dy) % L)
            if t != (0, 0):
                H[idx[t], n] += -lam
        # swap with the doublon: only from the four neighbours of the origin
        if (min(x, L - x) + min(y, L - y)) == 1:
            jx = x if x <= L // 2 else x - L
            jy = y if y <= L // 2 else y - L
            H[idx[((-x) % L, (-y) % L)], n] += lam * np.exp(-1j * (K[0] * jx + K[1] * jy))
    return H, sites
