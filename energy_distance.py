#!/usr/bin/env python3
"""
Energy-resolved particle separation: reproduces the
old/remake_2026-2/results/energy_distance_U*.png style, which shows the
two bands (extended B-band vs. bound U-band/pair states) most clearly.

Pair identification follows old/remake_2026-2: since the interaction
hyperplane r1=r2 has exactly L^2 = N sites, the U-band contains exactly
N states -- so we take the N eigenstates with the SMALLEST mean particle
separation <d> as "bound-pair states" (robust even for U=0, where there
is no energy gap to use as a separator).
"""

import numpy as np
import matplotlib.pyplot as plt

L = 7
LAM = 1.0
U_VALUES = [0.0, 10.0, 15.0, 20.0, 50.0]
OUT = "results"


def site_index(x, y):
    return (x % L) * L + (y % L)


def adjacency_matrix():
    N = L * L
    A = np.zeros((N, N))
    for x in range(L):
        for y in range(L):
            i = site_index(x, y)
            for nx, ny in [((x + 1) % L, y), ((x - 1) % L, y),
                           (x, (y + 1) % L), (x, (y - 1) % L)]:
                A[i, site_index(nx, ny)] += -LAM
    return A


def build_hamiltonian(A, U):
    N = A.shape[0]
    I = np.eye(N)
    H = np.kron(A, I) + np.kron(I, A)
    diag_idx = np.arange(N) * N + np.arange(N)
    H[diag_idx, diag_idx] += U
    return H


def distance_matrix():
    N = L * L
    D = np.zeros((N, N))
    for i in range(N):
        x1, y1 = divmod(i, L)
        for j in range(N):
            x2, y2 = divmod(j, L)
            dx = min(abs(x1 - x2), L - abs(x1 - x2))
            dy = min(abs(y1 - y2), L - abs(y1 - y2))
            D[i, j] = np.sqrt(dx * dx + dy * dy)
    return D


def average_distance(eigenvectors, D):
    N = D.shape[0]
    prob = np.abs(eigenvectors) ** 2          # (dim, nstates)
    Dflat = D.reshape(N * N)
    return Dflat @ prob                       # (nstates,)


def main():
    A = adjacency_matrix()
    D = distance_matrix()
    N = L * L

    for U in U_VALUES:
        print(f"U = {U:g}: diagonalizing (dim={N*N})...")
        H = build_hamiltonian(A, U)
        eigenvalues, eigenvectors = np.linalg.eigh(H)

        distances = average_distance(eigenvectors, D)

        # the N states with smallest <d> are the bound pair / U-band
        order = np.argsort(distances)
        pair_mask = np.zeros(len(eigenvalues), dtype=bool)
        pair_mask[order[:N]] = True
        bloch_mask = ~pair_mask

        print(
            f"  pair <d> range: [{distances[pair_mask].min():.4f}, "
            f"{distances[pair_mask].max():.4f}], "
            f"bloch mean <d> = {distances[bloch_mask].mean():.4f}"
        )

        fig, ax = plt.subplots(figsize=(10, 6))

        ax.scatter(
            eigenvalues[bloch_mask], distances[bloch_mask],
            s=8, alpha=0.35, color="royalblue", label="Extended states"
        )
        ax.scatter(
            eigenvalues[pair_mask], distances[pair_mask],
            s=30, color="crimson", label="Bound-pair states"
        )

        ax.set_xlabel(r"$E/\lambda$")
        ax.set_ylabel(r"$\langle d\rangle/a$")
        ax.set_title(f"Energy-resolved particle separation (L={L}, U={U:g})")
        ax.legend()
        ax.grid(alpha=0.2)
        fig.tight_layout()

        filename = f"{OUT}/energy_distance_U{U:g}.png"
        fig.savefig(filename, dpi=200)
        plt.close(fig)
        print(f"  Saved: {filename}")


if __name__ == "__main__":
    main()
