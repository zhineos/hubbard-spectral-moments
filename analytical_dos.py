#!/usr/bin/env python3
"""
Exact single-particle tight-binding density of states (DOS) for a
hypercubic lattice in d = 1, 2, 3, 4 dimensions, and comparison with the
numerically diagonalized two-electron Souza & Claro (2010) model.

Dispersion (lattice constant a=1, nearest-neighbour hopping lambda,
periodic boundary conditions):

    E_d(k) = -2*lambda * sum_{i=1}^d cos(k_i),   k_i in (-pi, pi]

Because the k_i are independent and uniformly distributed over the BZ,
E_d is the sum of d i.i.d. random variables X_i = -2*lambda*cos(k_i).
The density of states is therefore exactly the probability density of
that sum, which has the classic closed form (Economou, "Green's
Functions in Quantum Physics"; Morita 1971; Katsura & Inawashiro 1971):

    rho_d(E) = (1/pi) * Integral_0^inf  cos(E t) * [J_0(2*lambda*t)]^d  dt

with J_0 the zeroth-order Bessel function of the first kind. This is
exact for every d (it is just the Fourier inversion of the
characteristic function of a sum of independent arcsine-distributed
variables). For d=1 and d=2 it reduces to elementary/elliptic closed
forms; for d=3 and d=4 there is no elementary closed form, but the
integral above is evaluated here to machine-quadrature precision.

d=1: rho_1(E) = 1 / (pi * sqrt{(2 lambda)^2 - E^2}),      |E| < 2*lambda
     (inverse-square-root van Hove singularities at the band edges)

d=2: rho_2(E) = K( sqrt{1-(E/4lambda)^2} ) / (2*pi^2*lambda), |E|<4*lambda
     (K = complete elliptic integral of the 1st kind; logarithmic
      divergence at the band centre E=0, from the (pi,0)/(0,pi) saddles)

d=3: no elementary closed form; finite value at E=0 (related to the
     Watson-integral family for the simple cubic lattice Green's
     function), with a finite-slope kink (not a divergence) at E=0.

d=4: no elementary closed form; the DOS is smooth (no divergence
     anywhere) -- this is exactly the "bell shaped curve" the paper
     identifies as the U=0 two-electron DOS, since two independent
     electrons in 2D are mathematically identical to one particle
     hopping on a 4D hypercubic lattice.
"""

import warnings
import numpy as np
import matplotlib.pyplot as plt
from scipy.special import jv, ellipk
from scipy.integrate import quad

warnings.filterwarnings("ignore", category=Warning)

LAM = 1.0
OUT = "results"


# ================================================================
# EXACT CLOSED FORMS (d = 1, 2)
# ================================================================

def rho_1d(E, lam=LAM):
    E = np.atleast_1d(np.asarray(E, dtype=float))
    out = np.zeros_like(E)
    mask = np.abs(E) < 2 * lam
    out[mask] = 1.0 / (np.pi * np.sqrt((2 * lam) ** 2 - E[mask] ** 2))
    return out


def rho_2d(E, lam=LAM):
    E = np.atleast_1d(np.asarray(E, dtype=float))
    out = np.zeros_like(E)
    mask = np.abs(E) < 4 * lam
    m = 1.0 - (E[mask] / (4 * lam)) ** 2
    out[mask] = ellipk(m) / (2 * np.pi ** 2 * lam)
    return out


# ================================================================
# EXACT BESSEL-INTEGRAL FORM (any d; used here for d = 3, 4)
# ================================================================

def rho_bessel(E, d, lam=LAM, Tmax=500.0, limit=1000):
    def integrand(t):
        return jv(0, 2 * lam * t) ** d

    E = np.atleast_1d(np.asarray(E, dtype=float))
    out = np.zeros_like(E)
    for i, e in enumerate(E):
        val, _ = quad(integrand, 0, Tmax, weight="cos", wvar=e, limit=limit)
        out[i] = val / np.pi
    return out


def rho_3d(E, lam=LAM):
    return rho_bessel(E, 3, lam)


def rho_4d(E, lam=LAM):
    return rho_bessel(E, 4, lam)


RHO = {1: rho_1d, 2: rho_2d, 3: rho_3d, 4: rho_4d}

# d >= 5: [J_0(2*lambda*t)]^d decays even faster (~t^{-d/2}), so the
# same exact Bessel-integral representation is, if anything, easier to
# evaluate accurately than for d=3,4 -- no new formula needed.
for _d in (5, 6, 7, 8):
    RHO[_d] = (lambda E, lam=LAM, d=_d: rho_bessel(E, d, lam))


# ================================================================
# VALIDATION
# ================================================================

def validate():
    print("Validation (each curve should integrate to 1):")
    for d in (1, 2, 3, 4):
        edge = 2 * d * LAM
        grid = np.linspace(-edge * 0.9999, edge * 0.9999, 4000)
        vals = RHO[d](grid, LAM)
        integral = np.trapezoid(vals, grid)
        print(f"  d={d}:  integral = {integral:.5f}   "
              f"rho(0) = {RHO[d](np.array([0.0]), LAM)[0]:.5f}")
    print()


# ================================================================
# PLOT 1: the four analytical DOS curves together
# ================================================================

def plot_family(dims, filename, npts_per_dim=None):
    """
    Plot rho_d(E) for each d in `dims`, one panel per dimension, all
    sharing a common x-range set by the largest bandwidth in the group
    (so the panels are directly comparable).
    """
    dmax = max(dims)
    xlim = 2 * dmax * LAM

    fig, axes = plt.subplots(len(dims), 1, figsize=(7, 2.5 * len(dims)))
    if len(dims) == 1:
        axes = [axes]

    for ax, d in zip(axes, dims):
        edge = 2 * d * LAM
        n = 2000 if npts_per_dim is None else npts_per_dim.get(d, 2000)
        grid = np.linspace(-edge * 0.999, edge * 0.999, n)
        vals = RHO[d](grid, LAM)
        ax.plot(grid / LAM, vals, color="black", lw=1.3)
        ax.axvline(0, color="gray", lw=0.5, alpha=0.5)
        ax.set_xlim(-xlim, xlim)
        ax.set_ylabel(rf"$\rho_{{{d}D}}(E)$")
        ax.text(
            0.02, 0.85, f"d = {d}", transform=ax.transAxes,
            fontsize=11, fontweight="bold"
        )
        ax.grid(alpha=0.15)

    axes[-1].set_xlabel(r"$E\ (\lambda)$")
    fig.suptitle(
        "Exact single-particle tight-binding DOS, hypercubic lattice\n"
        r"$E_d(k)=-2\lambda\sum_{i=1}^d\cos k_i$, normalized to unit area",
        fontsize=11
    )
    fig.tight_layout(rect=[0, 0, 1, 0.95])
    fig.savefig(f"{OUT}/{filename}", dpi=200)
    print(f"Saved: {OUT}/{filename}")


# ================================================================
# PLOT 2: U=0 two-electron DOS vs analytical 4D DOS
# ================================================================

def gaussian_broadened(eigs, grid, sigma):
    dos = np.zeros_like(grid)
    for E in eigs:
        dos += np.exp(-0.5 * ((grid - E) / sigma) ** 2)
    dos /= (sigma * np.sqrt(2 * np.pi) * len(eigs))
    return dos


def two_electron_U0_eigs(L):
    """Dense diagonalization of the non-interacting two-electron
    Hamiltonian on an LxL periodic lattice (dimension (L^2)^2)."""

    def site_index(x, y):
        return (x % L) * L + (y % L)

    N = L * L
    A = np.zeros((N, N))
    for x in range(L):
        for y in range(L):
            i = site_index(x, y)
            for nx, ny in [((x + 1) % L, y), ((x - 1) % L, y),
                           (x, (y + 1) % L), (x, (y - 1) % L)]:
                A[i, site_index(nx, ny)] += -LAM

    I = np.eye(N)
    H = np.kron(A, I) + np.kron(I, A)
    return np.linalg.eigvalsh(H)


def plot_vs_U0():
    grid = np.linspace(-8 * LAM * 0.999, 8 * LAM * 0.999, 1000)
    analytic = rho_4d(grid, LAM)

    fig, ax = plt.subplots(figsize=(8, 5.5))

    eigs7 = np.loadtxt(f"{OUT}/eigenvalues_U0.dat")
    dos7 = gaussian_broadened(eigs7, grid, sigma=0.35)
    ax.plot(grid, dos7, color="tab:blue", lw=1.5, alpha=0.8,
            label=f"Numerical (L=7, N=49, dim={len(eigs7)})")

    print("Diagonalizing L=9, U=0 for the convergence check (dim=6561)...")
    eigs9 = two_electron_U0_eigs(9)
    dos9 = gaussian_broadened(eigs9, grid, sigma=0.25)
    ax.plot(grid, dos9, color="tab:green", lw=1.5, alpha=0.85,
            label=f"Numerical (L=9, N=81, dim={len(eigs9)})")

    ax.plot(
        grid, analytic, color="black", lw=2, ls="--",
        label="Analytical single-particle 4D DOS (continuum, L=$\\infty$)"
    )

    ax.set_xlabel(r"$E\ (\lambda)$")
    ax.set_ylabel("Normalized DOS")
    ax.set_title(
        "U=0: two independent electrons in 2D $\\equiv$ one particle in 4D"
    )
    ax.legend(fontsize=9)
    ax.grid(alpha=0.2)
    fig.tight_layout()
    fig.savefig(f"{OUT}/compare_U0_vs_4D.png", dpi=200)
    print(f"Saved: {OUT}/compare_U0_vs_4D.png")


# ================================================================
# PLOT 3: U-band DOS vs analytical 2D DOS (rescaled)
# ================================================================

def pair_theory(U, lam=LAM):
    """
    2nd-order degenerate perturbation theory on the paper's Eq. (4):
    the U-band is, to leading order in lambda/U, an effective 2D
    tight-binding band for the pair's centre-of-mass motion, with

        lambda_eff  = 2*lambda^2/U
        band centre = U + 8*lambda^2/U

    (derived from the on-site-defect/Koster-Slater bound-state condition
    1 = U*G_0(E;K), expanded to O(1/U); see SUMMARY item 24). No fitting
    -- both numbers are pure predictions from lambda and U alone.
    """
    lam_eff = 2.0 * lam ** 2 / U
    center = U + 8.0 * lam ** 2 / U
    return lam_eff, center


def plot_vs_Uband():
    fig, axes = plt.subplots(1, 3, figsize=(15, 5))

    for ax, U in zip(axes, (10.0, 15.0, 20.0)):
        # pool every available L for this U: different L sample the same
        # continuum pair-dispersion on different (denser) K-grids, so
        # pooling is a legitimate way to build a finer histogram
        pooled = []
        for L in (7, 9, 11):
            try:
                if L == 7:
                    eigs = np.loadtxt(f"{OUT}/eigenvalues_U{U:g}.dat")
                    band = eigs[eigs > 8.0 * LAM]
                else:
                    band = np.loadtxt(f"{OUT}/uband_L{L}_U{U:g}.dat")
                pooled.append(band)
            except OSError:
                pass
        band = np.concatenate(pooled)

        lam_eff, center = pair_theory(U, LAM)
        centered = band - center

        ax.hist(
            centered, bins=24, density=True, color="tab:red", alpha=0.5,
            label=f"Numerical U-band, pooled L=7,9,11 ({len(band)} states)"
        )

        grid = np.linspace(-4 * lam_eff * 0.999, 4 * lam_eff * 0.999, 800)
        analytic = rho_2d(grid, lam_eff)
        ax.plot(
            grid, analytic, color="black", lw=2,
            label=(
                r"2D DOS, theory: $\lambda_{eff}=2\lambda^2/U$"
                f"={lam_eff:.4f}$\\lambda$\n(no fitting)"
            )
        )

        ax.set_title(f"U = {U:g}$\\lambda$  (center = U+8$\\lambda^2$/U = {center:.3f})")
        ax.set_xlabel(r"$E - (U+8\lambda^2/U)\ (\lambda)$")
        ax.legend(fontsize=7.5)
        ax.grid(alpha=0.2)

    axes[0].set_ylabel("Normalized DOS")
    fig.suptitle(
        "U-band DOS vs. the theoretically predicted effective 2D DOS\n"
        r"$E_{pair}(K)\approx U+8\lambda^2/U-4\lambda^2/U\,(\cos K_x+\cos K_y)$"
        " -- zero free parameters",
        fontsize=11
    )
    fig.tight_layout(rect=[0, 0, 1, 0.90])
    fig.savefig(f"{OUT}/compare_Uband_vs_2D.png", dpi=200)
    print(f"Saved: {OUT}/compare_Uband_vs_2D.png")


if __name__ == "__main__":
    validate()
    plot_family([1, 2, 3, 4], "analytical_dos_1234D.png")
    plot_family([5, 6, 7, 8], "analytical_dos_5678D.png")
    plot_vs_U0()
    plot_vs_Uband()
