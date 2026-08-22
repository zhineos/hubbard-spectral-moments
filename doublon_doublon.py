#!/usr/bin/env python3
"""
Two doublons on a 2D lattice: Null 0 -> Null 1 -> Full hierarchy.

Everything is worked in units of t_d (the single-doublon hopping,
t_d = 2*lambda^2/U), so results here are UNIVERSAL -- they don't depend
on U or lambda separately, only through this one energy scale. To get
physical numbers for a specific U, multiply energies by t_d(U) and add
back 2*eps_d(U) (the two-doublon energy origin).

Following the paper's own Eq.(4) strategy one level up: at fixed total
(centre-of-mass) momentum K=(Kx,Ky) of the doublon PAIR, the relative
coordinate (u,v) between the two doublons obeys a single-particle-like
equation on the 2D lattice, with COM-momentum-dependent hopping
t_u = 2*t_d*cos(Kx), t_v = 2*t_d*cos(Ky) (same structure as the original
electron-pair problem, just with t_d replacing lambda).

Three levels of the theory, at the SAME K:

  Null 0 (free):      ordinary hopping on the full (u,v) lattice,
                       including the origin (u,v)=(0,0). This is just a
                       change of variables for two INDEPENDENT doublons;
                       pooling over K reproduces the exact analytical
                       rho_4D(E; t_d) from analytical_dos.py.

  Null 1 (hard-core):  same, but the origin site is REMOVED from the
                       Hilbert space entirely (D_R^2=0 -- two doublons
                       cannot occupy the same site, forbidden by Pauli
                       exclusion of the constituent electrons, no
                       dynamics involved). Quantifies the purely
                       kinematic/statistical effect.

  Full (hard-core+V_d): same as Null 1, plus an on-site energy V_d on the
                       four sites adjacent to the (removed) origin --
                       the leading dynamical doublon-doublon interaction,
                       predicted (and independently re-derived here via
                       explicit 2nd-order virtual-channel counting) to be
                       V_d = -4*lambda^2/U = -2*t_d.
"""

import numpy as np
import matplotlib.pyplot as plt

OUT = "results"

NN_OF_ORIGIN = [(1, 0), (-1, 0), (0, 1), (0, -1)]


# ================================================================
# PERIODIC relative lattice -- for DOS / continuum comparisons
# ================================================================

def site_index(u, v, L):
    return (u % L) * L + (v % L)


def relative_hamiltonian_periodic(L, Kx, Ky, hardcore, Vd, td=1.0):
    """
    L x L periodic relative lattice. If hardcore, the origin (0,0) is
    removed from the basis (dimension L^2-1); Vd is applied to its four
    neighbours. Matches the exact structure of the single-doublon
    relative-coordinate problem, one level up.
    """
    t_u = 2.0 * td * np.cos(Kx)
    t_v = 2.0 * td * np.cos(Ky)

    sites = [(u, v) for u in range(L) for v in range(L)]
    origin = (0, 0)
    if hardcore:
        sites = [s for s in sites if s != origin]
    index = {s: i for i, s in enumerate(sites)}
    N = len(sites)

    H = np.zeros((N, N))
    nn_set = set(NN_OF_ORIGIN) if Vd != 0.0 else set()

    for (u, v) in sites:
        i = index[(u, v)]
        if (u, v) in nn_set:
            H[i, i] += Vd
        for du, dv, t in ((1, 0, t_u), (-1, 0, t_u), (0, 1, t_v), (0, -1, t_v)):
            nb = ((u + du) % L, (v + dv) % L)
            if hardcore and nb == origin:
                continue
            H[i, index[nb]] += -t

    return H


def scan_dos(L, n_k, hardcore, Vd, td=1.0):
    ks = np.linspace(0, np.pi, n_k, endpoint=False) + (np.pi / n_k) / 2
    all_eigs = []
    for kx in ks:
        for ky in ks:
            H = relative_hamiltonian_periodic(L, kx, ky, hardcore, Vd, td)
            all_eigs.append(np.linalg.eigvalsh(H))
    return np.concatenate(all_eigs)


# ================================================================
# OPEN relative lattice -- for a clean bound-state search
# ================================================================

def relative_hamiltonian_open(L_half, Kx, Ky, hardcore, Vd, td=1.0):
    """
    Open-boundary relative lattice, u,v in [-L_half,L_half], origin at
    the centre. Open BC avoids periodic-image artefacts when hunting for
    a state exponentially localized near the origin.
    """
    t_u = 2.0 * td * np.cos(Kx)
    t_v = 2.0 * td * np.cos(Ky)

    rng = range(-L_half, L_half + 1)
    sites = [(u, v) for u in rng for v in rng]
    origin = (0, 0)
    if hardcore:
        sites = [s for s in sites if s != origin]
    index = {s: i for i, s in enumerate(sites)}
    N = len(sites)

    H = np.zeros((N, N))
    nn_set = set(NN_OF_ORIGIN) if Vd != 0.0 else set()

    for (u, v) in sites:
        i = index[(u, v)]
        if (u, v) in nn_set:
            H[i, i] += Vd
        for du, dv, t in ((1, 0, t_u), (-1, 0, t_u), (0, 1, t_v), (0, -1, t_v)):
            nb = (u + du, v + dv)
            if nb in index:
                H[i, index[nb]] += -t

    return H, sites, index


if __name__ == "__main__":
    import sys
    print("Module loaded. Use companion scripts to run the DOS scan and "
          "bound-state search.")
