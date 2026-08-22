#!/usr/bin/env python3
"""
Exact infinite-lattice T-matrix / Green's-function calculation for two
hard-core doublons with a nearest-neighbour attraction V_d, at fixed
total (centre-of-mass) momentum Q=(Qx,Qy).

This replaces the finite-box diagonalization in doublon_doublon.py with
an exact statement about the INFINITE lattice, so it can resolve
arbitrarily shallow binding energies with no box-size ambiguity.

Setup (relative coordinate r=(u,v) between the two doublons, everything
in units of t_d):

  free dispersion   eps0(q;Q) = -2*t_u*cos(qu) - 2*t_v*cos(qv)
                     t_u = 2*cos(Qx), t_v = 2*cos(Qy)   (t_d=1 units)

  free lattice Green's function (site difference Delta, energy E):
                     g(Delta; E, Q) = Integral d^2q/(2pi)^2
                                       cos(qu*Du)*cos(qv*Dv) / (E - eps0)

The perturbation is: (1) an infinite on-site repulsion at the origin
r=0 (hard-core: two doublons cannot coincide), and (2) V_d on the four
sites r = (+-1,0), (0,+-1).

Step 1 -- remove the origin site exactly (standard single-site T-matrix,
Lambda -> infinity limit): the "vacancy" Green's function between any
two OTHER sites is

  G_vac(r,r';E) = g(r-r';E) - g(r;E)*g(r';E) / g(0;E)

(g(r;E) here means g(r-0;E), the propagator from the origin).

Step 2 -- put V_d on the four nearest-neighbour sites of the (now
excluded) origin, using G_vac restricted to those four sites. The
bound-state condition is the small determinant

  det[ I_4 - V_d * G_vac(NN,NN;E,Q) ] = 0

for E outside the continuum. By the square-lattice site symmetries,
G_vac(NN,NN) depends on only four independent numbers (g00, ga, gb, gaa,
gbb, gab below), so this is cheap to evaluate at any (E,Q).
"""

import numpy as np

TD = 1.0  # everything in units of t_d


def continuum_range(Qx, Qy, td=TD):
    t_u = 2.0 * td * np.cos(Qx)
    t_v = 2.0 * td * np.cos(Qy)
    half = 2.0 * (abs(t_u) + abs(t_v))
    return -half, half


def green_values(E, Qx, Qy, n=2000, td=TD):
    """
    Returns (g00, ga, gb, gaa, gbb, gab) -- the free lattice Green's
    function at site separations (0,0), (1,0), (0,1), (2,0), (0,2),
    (1,1), evaluated via a fine Riemann sum over the Brillouin zone
    (exact in the n->infinity limit; E must lie outside the continuum
    for the integrand to be non-singular).
    """
    t_u = 2.0 * td * np.cos(Qx)
    t_v = 2.0 * td * np.cos(Qy)

    q = np.linspace(-np.pi, np.pi, n, endpoint=False)
    QU, QV = np.meshgrid(q, q, indexing="ij")
    eps = -2.0 * t_u * np.cos(QU) - 2.0 * t_v * np.cos(QV)
    denom = E - eps
    w = 1.0 / (n * n)   # (dq)^2/(2pi)^2 = 1/n^2 exactly on this grid

    g00 = np.sum(1.0 / denom) * w
    ga = np.sum(np.cos(QU) / denom) * w
    gb = np.sum(np.cos(QV) / denom) * w
    gaa = np.sum(np.cos(2 * QU) / denom) * w
    gbb = np.sum(np.cos(2 * QV) / denom) * w
    gab = np.sum(np.cos(QU) * np.cos(QV) / denom) * w
    return g00, ga, gb, gaa, gbb, gab


def vacancy_matrix(E, Qx, Qy, n=2000, td=TD):
    """4x4 vacancy-corrected Green's function among the NN sites,
    basis order [+x, -x, +y, -y]."""
    g00, ga, gb, gaa, gbb, gab = green_values(E, Qx, Qy, n, td)

    G0 = np.array([
        [g00, gaa, gab, gab],
        [gaa, g00, gab, gab],
        [gab, gab, g00, gbb],
        [gab, gab, gbb, g00],
    ])
    v = np.array([ga, ga, gb, gb])

    M = G0 - np.outer(v, v) / g00
    return M


def det_condition(E, Vd, Qx, Qy, n=2000, td=TD):
    M = vacancy_matrix(E, Qx, Qy, n, td)
    return np.linalg.det(np.eye(4) - Vd * M)


def find_bound_state(Vd, Qx, Qy, n=1500, td=TD, search_below=3.0, npts=400):
    """
    Scan E from (continuum_bottom - search_below) up to continuum_bottom
    and look for a sign change in det_condition (a bound state splitting
    off below the continuum). Returns the bound-state energy, or None.
    """
    lo, hi = continuum_range(Qx, Qy, td)
    Es = np.linspace(lo - search_below, lo - 1e-4, npts)
    vals = np.array([det_condition(E, Vd, Qx, Qy, n, td) for E in Es])

    sign_changes = np.where(np.diff(np.sign(vals)) != 0)[0]
    if len(sign_changes) == 0:
        return None, lo

    # refine the lowest-|E| (i.e. closest to threshold) crossing via bisection
    i = sign_changes[-1]
    a, b = Es[i], Es[i + 1]
    fa = det_condition(a, Vd, Qx, Qy, n, td)
    for _ in range(60):
        m = 0.5 * (a + b)
        fm = det_condition(m, Vd, Qx, Qy, n, td)
        if np.sign(fm) == np.sign(fa):
            a, fa = m, fm
        else:
            b = m
    return 0.5 * (a + b), lo


if __name__ == "__main__":
    print("Module loaded.")
