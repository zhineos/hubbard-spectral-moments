#!/usr/bin/env python3
"""
Reproduction of Fig. 1 of Souza & Claro (2010), arXiv:1005.1857.

Two interacting tight-binding electrons on a 7x7 (N=49 site) periodic
square lattice. Full dense diagonalization (Hilbert dimension 49^2 = 2401)
for U = 0, 10, 15, 20 lambda, stacked DOS panels matching the paper's
Fig. 1 layout.

H = -lambda * (hopping of particle 1 + hopping of particle 2)
    + U * delta(r1, r2)
"""

import numpy as np
import matplotlib.pyplot as plt

L = 7
LAM = 1.0
U_VALUES = [0.0, 10.0, 15.0, 20.0]   # bottom -> top panel, matches Fig. 1
SIGMA = 0.35                         # Gaussian broadening width
N_GRID = 2000

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
    # interaction: U on the diagonal subspace r1 == r2
    diag_idx = np.arange(N) * N + np.arange(N)
    H[diag_idx, diag_idx] += U
    return H


def gaussian_dos(energies, grid, sigma):
    dos = np.zeros_like(grid)
    for E in energies:
        dos += np.exp(-0.5 * ((grid - E) / sigma) ** 2)
    dos /= (sigma * np.sqrt(2 * np.pi))
    return dos


def main():
    print("Building adjacency matrix (L=7, N=49 sites)...")
    A = adjacency_matrix()

    Emin, Emax = -10.0, 25.0
    grid = np.linspace(Emin, Emax, N_GRID)

    all_energies = {}
    for U in U_VALUES:
        print(f"Diagonalizing U = {U:g} lambda (dim=2401)...")
        H = build_hamiltonian(A, U)
        eigenvalues = np.linalg.eigvalsh(H)
        all_energies[U] = eigenvalues
        print(
            f"  E range: {eigenvalues.min():.4f} -> {eigenvalues.max():.4f}, "
            f"states above 8*lambda: {int(np.sum(eigenvalues > 8 * LAM))}"
        )

    fig, axes = plt.subplots(
        len(U_VALUES), 1, figsize=(7, 9), sharex=True
    )

    # paper orders panels bottom (U=0) to top (U=20 lambda)
    for ax, U in zip(reversed(axes), U_VALUES):
        dos = gaussian_dos(all_energies[U], grid, SIGMA)
        # rescale to arbitrary units similar to the paper's peak height (~8)
        dos = dos / dos.max() * 8.0
        ax.plot(grid, dos, color="black", lw=1.2)
        ax.set_ylim(0, 9)
        ax.set_yticks([0, 4, 8])
        ax.text(
            0.97, 0.85, f"U = {U:g}" + (r"$\lambda$" if U > 0 else ""),
            transform=ax.transAxes, ha="right", va="top", fontsize=11
        )
        ax.grid(alpha=0.15)

    axes[-1].set_xlabel(r"$E\ (\lambda)$")
    axes[len(axes) // 2].set_ylabel("DOS (arb. units)")
    fig.suptitle(
        "Reproduction of Fig. 1 — Souza & Claro (2010)\n"
        "Two-electron DOS, 7x7 lattice (N=49), periodic BC",
        fontsize=11
    )
    fig.tight_layout(rect=[0, 0, 1, 0.94])

    filename = f"{OUT}/fig1_dos_reproduction.png"
    fig.savefig(filename, dpi=200)
    print(f"Saved: {filename}")

    for U in U_VALUES:
        np.savetxt(
            f"{OUT}/eigenvalues_U{U:g}.dat",
            all_energies[U],
            header="eigenvalue (lambda)"
        )


if __name__ == "__main__":
    main()
