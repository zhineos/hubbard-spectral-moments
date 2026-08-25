#!/usr/bin/env python3
"""
Twisted-boundary-condition (TBC) averaging to get much better numerical
DOS estimates, for comparison with the exact analytical curves in
analytical_dos.py.

TWO complementary uses of the same idea (a boundary-phase twist shifts
the discrete allowed momenta k_n = 2*pi*n/L by an offset theta/L,
without changing the size of the Hamiltonian at all):

1. U=0 (non-interacting) case
   ---------------------------
   The two-electron problem at U=0 is EXACTLY separable: the full
   two-particle spectrum is every pairwise sum eps_n1+eps_n2 of the
   SAME single-particle spectrum {eps_n} (Kronecker-sum eigenvalues of
   H = A(x)I + I(x)A). So instead of ever diagonalizing the (L^2)^2
   two-particle Hamiltonian, we only need the L^2 eigenvalues of the
   L^2 x L^2 single-particle adjacency matrix -- for hundreds of random
   twists this is essentially free, and because a single-particle
   twist continuously shifts its OWN momenta over the full Brillouin
   zone, twist-averaging converges very fast (much faster than
   increasing L at fixed BC) to the exact continuum 4D DOS.

2. U>0 (interacting / U-band) case
   --------------------------------
   The interaction breaks the product structure, so we can't avoid
   diagonalizing something two-body. But the paper's own Eq. (4)
   already reduces the two-body problem, at FIXED centre-of-mass
   momentum K=(kx,ky), to a single-particle-like problem on the
   relative-coordinate (u,v) lattice with an on-site defect U at the
   origin and COM-momentum-dependent hopping t_u=2*lambda*cos(kx),
   t_v=2*lambda*cos(ky) (dimension L_rel^2, decoupled from the size of
   the original two-particle problem). Scanning (kx,ky) on a fine
   continuous grid is *exactly* a continuum of twisted boundary
   conditions on the centre-of-mass motion, and is far cheaper than
   diagonalizing the full two-particle Hamiltonian at many twists,
   since each relative-coordinate problem is only L_rel^2-dimensional.
   The single extra eigenvalue pushed above the continuum by the
   repulsive on-site U (for U large enough) is the U-band energy at
   that K -- collecting it over a fine K-grid gives a near-continuum
   U-band DOS to test the analytical_dos.py pair_theory() prediction.
"""

import numpy as np
import matplotlib.pyplot as plt

import analytical_dos as ad
import plotstyle as ps

ps.apply()

LAM = 1.0
OUT = "results"
RNG = np.random.default_rng(12345)


# ================================================================
# 1. TWISTED SINGLE-PARTICLE PROBLEM (U=0 case)
# ================================================================

def site_index(x, y, L):
    return x * L + y


def twisted_adjacency(L, theta_x, theta_y, lam=LAM):
    N = L * L
    A = np.zeros((N, N), dtype=complex)
    for x in range(L):
        for y in range(L):
            i = site_index(x, y, L)

            if x + 1 < L:
                A[i, site_index(x + 1, y, L)] += -lam
            else:
                A[i, site_index(0, y, L)] += -lam * np.exp(1j * theta_x)

            if x - 1 >= 0:
                A[i, site_index(x - 1, y, L)] += -lam
            else:
                A[i, site_index(L - 1, y, L)] += -lam * np.exp(-1j * theta_x)

            if y + 1 < L:
                A[i, site_index(x, y + 1, L)] += -lam
            else:
                A[i, site_index(x, 0, L)] += -lam * np.exp(1j * theta_y)

            if y - 1 >= 0:
                A[i, site_index(x, y - 1, L)] += -lam
            else:
                A[i, site_index(x, L - 1, L)] += -lam * np.exp(-1j * theta_y)

    return A


def tbc_two_particle_energies_U0(L, n_twists, lam=LAM, independent=True):
    """
    Pool the exact (product-structure) two-particle spectrum over many
    random boundary twists. Each twist costs one L^2 x L^2 dense
    Hermitian diagonalization (cheap) and yields N^2=L^4 two-particle
    energies for free (all pairwise sums).

    independent=True draws a SEPARATE random twist for each of the two
    electrons before forming pairwise sums. This is not a physical
    "shared boundary condition" any more, but at U=0 the two electrons
    are exactly independent anyway, so it is a valid (and far more
    effective) Monte-Carlo estimator for the exact convolution/continuum
    DOS: a single SHARED twist only ever moves both particles' momenta
    together (a 2-parameter family embedded in the full 4D BZ), so
    pooling many shared-twist draws barely improves on the fixed-BC
    result; independent twists sample the full 4D BZ i.i.d., which is
    exactly what the target distribution (a sum of two independent
    single-particle energies) requires.
    """
    all_energies = []
    for _ in range(n_twists):
        theta_x1, theta_y1 = RNG.uniform(0, 2 * np.pi, size=2)
        eps1 = np.linalg.eigvalsh(twisted_adjacency(L, theta_x1, theta_y1, lam))

        if independent:
            theta_x2, theta_y2 = RNG.uniform(0, 2 * np.pi, size=2)
            eps2 = np.linalg.eigvalsh(twisted_adjacency(L, theta_x2, theta_y2, lam))
        else:
            eps2 = eps1

        pair = (eps1[:, None] + eps2[None, :]).ravel()
        all_energies.append(pair)
    return np.concatenate(all_energies)


# ================================================================
# 2. RELATIVE-COORDINATE PROBLEM (U-band case, paper's Eq. 4)
# ================================================================

def relative_hamiltonian(L_rel, kx, ky, U, lam=LAM):
    N = L_rel * L_rel
    H = np.zeros((N, N))
    t_u = 2.0 * lam * np.cos(kx)
    t_v = 2.0 * lam * np.cos(ky)

    for u in range(L_rel):
        for v in range(L_rel):
            i = site_index(u, v, L_rel)
            if u == 0 and v == 0:
                H[i, i] += U
            for un in ((u + 1) % L_rel, (u - 1) % L_rel):
                H[i, site_index(un, v, L_rel)] += -t_u
            for vn in ((v + 1) % L_rel, (v - 1) % L_rel):
                H[i, site_index(u, vn, L_rel)] += -t_v

    return H


def uband_dispersion_scan(L_rel, U, n_k, lam=LAM):
    """
    Scan the paper's kx,ky (each in [0,pi], cos is even/periodic so this
    covers all distinct hopping amplitudes) on an n_k x n_k grid. For
    each K, return the single eigenvalue pushed above the continuum by
    the repulsive on-site defect U (the U-band / bound-pair energy).
    """
    ks = np.linspace(0, np.pi, n_k, endpoint=False) + (np.pi / n_k) / 2
    energies = np.zeros((n_k, n_k))
    for i, kx in enumerate(ks):
        for j, ky in enumerate(ks):
            H = relative_hamiltonian(L_rel, kx, ky, U, lam)
            w = np.linalg.eigvalsh(H)
            energies[i, j] = w[-1]   # top eigenvalue = U-band state
    return energies.ravel()


# ================================================================
# PLOT: U=0 TBC-averaged DOS vs exact continuum 4D DOS
# ================================================================

def plot_tbc_U0(L=9, n_twists=300):
    print(f"TBC-averaging U=0 DOS: L={L}, {n_twists} random twists "
          f"({L*L} sites, {(L*L)**2} two-particle states per twist)...")

    pooled = tbc_two_particle_energies_U0(L, n_twists)
    print(f"  Pooled {len(pooled)} two-particle energies "
          f"({n_twists} twists x {(L*L)**2} states/twist).")

    grid = np.linspace(-8 * LAM * 0.999, 8 * LAM * 0.999, 1000)
    analytic = ad.rho_4d(grid, LAM)

    # fixed-BC (theta=0) reference, same L, for comparison
    fixed = tbc_two_particle_energies_U0.__wrapped__ if False else None
    A0 = twisted_adjacency(L, 0.0, 0.0, LAM)
    eps0 = np.linalg.eigvalsh(A0).real
    fixed_energies = (eps0[:, None] + eps0[None, :]).ravel()

    sigma_tbc = 0.06
    sigma_fixed = 0.35
    dos_tbc = ad.gaussian_broadened(pooled, grid, sigma=sigma_tbc)
    dos_fixed = ad.gaussian_broadened(fixed_energies, grid, sigma=sigma_fixed)

    fig, ax = plt.subplots(figsize=(ps.FIGWIDTH_SINGLE, 4.4),
                            constrained_layout=True)

    # Visual hierarchy matches the physics narrative: finite periodic
    # spectrum (secondary, background) -> twist averaging (the result
    # being tested) -> continuum analytic curve (the reference to test
    # against). The twist-averaged curve is rendered as sparse markers,
    # not another line, so agreement/disagreement with the analytic
    # curve is falsifiable point-by-point rather than "one line sitting
    # under another." All quantitative detail (L, state counts, twist
    # count) lives in the caption, not on the plot itself.
    ax.plot(grid, dos_fixed, color="0.75", lw=1.0, alpha=0.9, zorder=1,
            label="Periodic BC")

    stride = 18
    ax.plot(grid[::stride], dos_tbc[::stride], "o", color=ps.C_CONNECTIVITY,
            ms=4.2, mec="white", mew=0.4, zorder=3,
            label="Twist averaged")

    ax.plot(grid, analytic, color=ps.C_NEUTRAL, lw=1.6, ls=ps.LS_THEORY,
            zorder=2, label="Exact (4D) DOS")

    ax.set_xlabel(r"$E\ (\lambda)$")
    ax.set_ylabel("Normalized DOS")
    ax.legend(fontsize=8, loc="upper right", frameon=False)
    ax.set_title(r"$U=0$ two-electron DOS", fontsize=11)
    ps.style_axes(ax)
    fig.savefig(f"{OUT}/tbc_compare_U0_vs_4D.png")
    print(f"Saved: {OUT}/tbc_compare_U0_vs_4D.png")
    print(f"  Caption should state: L={L} periodic square lattice; "
          f"fixed-boundary spectrum contains {(L*L)**2} states; "
          f"averaging over {n_twists} independent boundary twists gives "
          f"{len(pooled)} eigenvalues.")

    # quantitative fit quality
    rmse_tbc = np.sqrt(np.mean((dos_tbc - analytic) ** 2))
    rmse_fixed = np.sqrt(np.mean((dos_fixed - analytic) ** 2))
    print(f"  RMSE vs analytic: fixed-BC={rmse_fixed:.5f}  "
          f"twist-averaged={rmse_tbc:.5f}  "
          f"(improvement: {rmse_fixed/rmse_tbc:.1f}x)")


# ================================================================
# U-band exact-K-grid DOS vs 2nd-order perturbation theory
# ================================================================

def scan_all(U_values, L_rel=21, n_k=48):
    """Run the exact K-grid scan once per U and cache the results."""
    results = {}
    for U in U_values:
        print(f"Scanning K-grid for U={U:g} (L_rel={L_rel}, "
              f"{n_k}x{n_k} K-points)...")
        E = uband_dispersion_scan(L_rel, U, n_k)
        lam_eff, center = ad.pair_theory(U, LAM)
        print(
            f"  U={U:g}: E range [{E.min():.5f},{E.max():.5f}], "
            f"predicted center={center:.5f}, "
            f"predicted half-width={4*lam_eff:.5f}"
        )
        results[U] = E
    return results


def plot_kgrid_Uband(scans, L_rel, n_k):
    n = len(scans)
    fig, axes = plt.subplots(1, n, figsize=(5 * n, 5))
    if n == 1:
        axes = [axes]

    for ax, U in zip(axes, scans):
        E = scans[U]
        lam_eff, center = ad.pair_theory(U, LAM)
        centered = E - center

        ax.hist(
            centered, bins=60, density=True, color="tab:green", alpha=0.55,
            label="Exact"
        )

        grid = np.linspace(-4 * lam_eff * 0.999, 4 * lam_eff * 0.999, 800)
        analytic = ad.rho_2d(grid, lam_eff)
        ax.plot(
            grid, analytic, color="black", lw=2,
            label="2D DOS prediction"
        )

        ax.set_title(f"$U = {U:g}\\lambda$")
        ax.set_xlabel(r"$E - \varepsilon_d\ (\lambda)$")
        ax.legend(fontsize=7.5, frameon=False)
        ax.grid(alpha=0.2)

    axes[0].set_ylabel("Normalized DOS")
    fig.tight_layout()
    fig.savefig(f"{OUT}/kgrid_compare_Uband_vs_2D.png", dpi=200)
    print(f"Saved: {OUT}/kgrid_compare_Uband_vs_2D.png")
    print(f"  Caption should state: exact relative-coordinate K-grid scan "
          f"(L_rel={L_rel}, {n_k}x{n_k} K-points) vs. the parameter-free "
          f"2nd-order prediction (Eq.~(4)), U={sorted(scans.keys())}lambda, "
          f"no fitted parameters.")


# ================================================================
# Universal data collapse: x = (E - E_c) / (2*lambda_eff)
# ================================================================

def rho_universal(x):
    """
    rho_2D(E; lambda_eff) rewritten in the rescaled variable
    x = (E-E_c)/(2*lambda_eff) is independent of lambda_eff (and hence
    of U): rho~(x) = K(1-(x/2)^2) / pi^2 on the fixed support |x|<2 --
    every U should collapse onto this single universal curve.
    """
    x = np.atleast_1d(np.asarray(x, dtype=float))
    return 2.0 * ad.rho_2d(2.0 * x, 1.0)


def plot_kgrid_collapse(scans):
    # Notation matches the manuscript's Sec. 2 exactly: t_d=2*lam^2/U,
    # eps_d=U+8*lam^2/U (pair_theory returns (t_d, eps_d) under the
    # internal names lam_eff/center; only the DISPLAYED labels change
    # here, not the underlying quantities).
    fig, ax = plt.subplots(figsize=(ps.FIGWIDTH_SINGLE + 1.6, 4.2),
                            constrained_layout=True)

    U_sorted = sorted(scans.keys())
    shades = ps.doublon_shades(len(U_sorted))
    markers = ps.MARKERS[:len(U_sorted)]

    for U, color, marker in zip(U_sorted, shades, markers):
        E = scans[U]
        t_d, eps_d = ad.pair_theory(U, LAM)
        x = (E - eps_d) / (2.0 * t_d)

        hist, edges = np.histogram(x, bins=50, range=(-2, 2), density=True)
        centers = 0.5 * (edges[:-1] + edges[1:])
        ax.plot(
            centers, hist, marker, ms=3.5, lw=1.1, color=color,
            label=rf"$U={U:g}\lambda,\ t_d={t_d:.4f}\lambda$"
        )

    xg = np.linspace(-1.999, 1.999, 800)
    ax.plot(xg, rho_universal(xg), color=ps.C_NEUTRAL, lw=1.8, ls=ps.LS_THEORY,
            label=r"Exact (2D) DOS $\rho_{2D}(x)$")

    ax.set_xlabel(r"$x = (E-\varepsilon_d)/(2t_d)$")
    ax.set_ylabel(r"$\tilde\rho_U(x)$")
    ax.set_title(
        r"Data collapse: $U\to\infty \Rightarrow \tilde\rho_U(x)\to\rho_{2D}(x)$",
        fontsize=10.5,
    )
    ax.legend(fontsize=8.5, loc="upper left", bbox_to_anchor=(1.02, 1.0),
              borderaxespad=0)
    ps.style_axes(ax)
    fig.savefig(f"{OUT}/kgrid_collapse_universal.png")
    print(f"Saved: {OUT}/kgrid_collapse_universal.png")
    print("  Caption should state: no fitted parameters -- t_d, eps_d "
          "both predicted directly from U, lambda.")


if __name__ == "__main__":
    plot_tbc_U0(L=9, n_twists=300)
    print()

    L_rel, n_k = 21, 48
    scans = scan_all((10.0, 15.0, 20.0, 50.0), L_rel=L_rel, n_k=n_k)
    plot_kgrid_Uband(scans, L_rel, n_k)
    plot_kgrid_collapse(scans)
