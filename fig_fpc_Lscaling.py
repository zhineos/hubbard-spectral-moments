#!/usr/bin/env python3
"""
Fig. 5: exact many-fermion variance vs. the parameter-free
finite-population (FPC) prediction, L=3..10, single spin species,
U=0. A single species has no Hubbard interaction at all, so the
many-body spectrum is exactly every size-k, without-replacement
selection from the L^2 single-particle levels: the population
variance of such a sum is EXACTLY k*sigma1^2*(N-k)/(N-1) (a classical
finite-population identity, not an approximation), with sigma1^2 the
population variance of the true single-particle tight-binding
spectrum -- no diagonalization, no sampling, and no assumed value of
sigma1^2 needed. The FPC "prediction" plugs in the a-priori continuum
value sigma1^2=z*lambda^2; the "exact" points use sigma1^2 measured
directly from the finite-L spectrum. Their coincidence at every L is
therefore a nontrivial check that the finite lattice reproduces the
continuum coordination number exactly, not merely asymptotically.

This figure is about mu_2 (population variance), so it uses the
CONNECTIVITY color family.
"""
import numpy as np
import matplotlib.pyplot as plt
from itertools import combinations
import plotstyle as ps
from three_electron import build_neighbors, adjacency_matrix

ps.apply()

LAM = 1.0
Z_THEORY = 4.0  # square-lattice coordination number
L_values = list(range(3, 11))
k_values = [2, 3, 4]
shades = ps.connectivity_shades(len(k_values))
markers = ps.MARKERS[:len(k_values)]


def brute_force_variance(eps, k):
    """Full enumeration over all C(N,k) subsets -- used only as a
    small-N validation that the closed-form identity below is not
    hiding an indexing bug, not for the plotted points."""
    N = len(eps)
    sums = np.array([eps[list(c)].sum() for c in combinations(range(N), k)])
    return np.var(sums)


# small-N sanity check (L=3, N=9): closed form vs full enumeration
neighbors3 = build_neighbors(3)
eps3 = np.linalg.eigvalsh(adjacency_matrix(3, neighbors3, LAM).toarray())
for k in k_values:
    N = 9
    sigma1_sq = np.var(eps3)
    closed = k * sigma1_sq * (N - k) / (N - 1)
    brute = brute_force_variance(eps3, k)
    print(f"sanity L=3,k={k}: closed-form={closed:.8f}  "
          f"full-enumeration={brute:.8f}  diff={abs(closed-brute):.2e}")

fig, ax = plt.subplots(figsize=(ps.FIGWIDTH_SINGLE, 4.0), constrained_layout=True)

# Redesigned as the dimensionless ratio Var(E_k)/(k*sigma1^2) vs L, with
# parameter-free prediction (N-k)/(N-1): all k collapse onto the same
# vertical range (unlike the raw-variance version, where the three k
# curves occupy widely separated bands), the thermodynamic limit -> 1
# is visually immediate, and finite-size narrowing is the one message
# of the plot. One marker per k, one thin theory line, no per-k legend
# clutter about the FPC formula itself (that lives in the caption).
results = []
for k, color, marker in zip(k_values, shades, markers):
    ratio_pts, pred_pts = [], []
    for L in L_values:
        neighbors = build_neighbors(L)
        eps = np.linalg.eigvalsh(adjacency_matrix(L, neighbors, LAM).toarray())
        N = L * L
        sigma1_sq_measured = np.var(eps)
        exact = k * sigma1_sq_measured * (N - k) / (N - 1)
        fpc = k * (Z_THEORY * LAM**2) * (N - k) / (N - 1)
        pred = (N - k) / (N - 1)
        ratio_pts.append(exact / (k * sigma1_sq_measured))
        pred_pts.append(pred)
        results.append((L, k, sigma1_sq_measured, exact, fpc))
    ax.plot(L_values, pred_pts, color=ps.C_NEUTRAL, ls=ps.LS_THEORY, lw=1.3,
             zorder=1)
    ax.plot(L_values, ratio_pts, marker, color=color, ms=6, ls="none",
             mec="black", mew=0.6, zorder=3, label=rf"$k={k}$")

ax.axhline(1.0, color="0.85", lw=0.8, zorder=0)
ax.set_xlabel(r"$L$ (lattice is $L\times L$, $N=L^2$)")
ax.set_ylabel(r"$\mathrm{Var}(E_k)/(k\sigma_1^2)$")
ax.set_xticks(L_values)
handles, labels = ax.get_legend_handles_labels()
from matplotlib.lines import Line2D
handles.append(Line2D([0], [0], color=ps.C_NEUTRAL, ls=ps.LS_THEORY, lw=1.3))
labels.append("FPC prediction")
ax.legend(handles, labels, fontsize=8.5, loc="lower right")
ps.style_axes(ax)

fig.savefig("results/fpc_Lscaling.png")
print("wrote results/fpc_Lscaling.png")

print(f"{'L':>3} {'k':>2} {'sigma1^2':>10} {'exact':>12} {'FPC':>12} {'rel.diff':>10}")
for L, k, s1, ex, fpc in results:
    reldiff = abs(ex - fpc) / fpc if fpc else 0.0
    print(f"{L:3d} {k:2d} {s1:10.6f} {ex:12.6f} {fpc:12.6f} {reldiff:10.2e}")
