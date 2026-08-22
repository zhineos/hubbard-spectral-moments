#!/usr/bin/env python3
"""
U-band eigenstates at larger L via shift-invert sparse diagonalization.

This fixes the bug found in remake_2026-sparse/dos_distance.py (SUMMARY
item 21c): requesting eigsh(..., which="SA") only returns the most
NEGATIVE eigenvalues, which never reach the U-band (it sits near E~U,
at the top of the spectrum). Here we shift-invert around sigma=U, which
targets exactly the eigenvalues closest to U -- i.e. the U-band itself
(known to contain exactly L^2 states).
"""

import numpy as np
from scipy.sparse import lil_matrix, csr_matrix, identity
from scipy.sparse.linalg import eigsh

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


def build_hamiltonian(L, U, neighbors, lam=LAM):
    N = L * L
    dim = N * N
    H = lil_matrix((dim, dim), dtype=float)

    def state(i, j):
        return i * N + j

    for i in range(N):
        for j in range(N):
            p = state(i, j)
            if i == j:
                H[p, p] += U
            for ni in neighbors[i]:
                H[p, state(ni, j)] += -lam
            for nj in neighbors[j]:
                H[p, state(i, nj)] += -lam

    return csr_matrix(H)


def uband_eigenvalues(L, U, lam=LAM):
    N = L * L
    neighbors = build_neighbors(L)
    H = build_hamiltonian(L, U, neighbors, lam)
    k = N  # the U-band contains exactly L^2 = N states

    eigenvalues = eigsh(
        H, k=k, sigma=U, which="LM", mode="normal",
        return_eigenvectors=False
    )
    return np.sort(eigenvalues)


def main():
    results = {}
    for L in (9, 11, 13):
        for U in (10.0, 15.0, 20.0):
            print(f"L={L:2d}  U={U:5.1f}  dim={(L*L)**2:6d} ...", end=" ", flush=True)
            eigs = uband_eigenvalues(L, U)
            below_U = int(np.sum(eigs < U - 1e-6))
            print(
                f"got {len(eigs)} states, range [{eigs.min():.4f}, {eigs.max():.4f}], "
                f"{below_U} below U (should be 0)"
            )
            results[(L, U)] = eigs
            np.savetxt(f"{OUT}/uband_L{L}_U{U:g}.dat", eigs,
                       header=f"U-band eigenvalues, L={L}, U={U}, shift-invert sigma=U")


if __name__ == "__main__":
    main()
