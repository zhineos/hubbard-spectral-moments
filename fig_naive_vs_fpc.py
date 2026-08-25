#!/usr/bin/env python3
"""
Fig. 7: naive vs. FPC-corrected reference, both against the exact
U=infinity mu2 theorem, for every N_d=0 sector tested at n=2,3,4
(L=4). Three panels: (a) naive isotropic-2C-D reference vs exact;
(b) finite-population (exchange) corrected reference vs exact; (c)
the full real-space projection (Gutzwiller) reference vs exact.
Panel (b)'s residual for mixed-spin compositions is exactly the
real-space effect derived in the main text (Sec. V) -- not a failure
of the exchange correction, but evidence of a distinct mechanism.

This figure is fundamentally about mu_2 (connectivity), so it uses the
CONNECTIVITY color throughout: filled markers for single-species
compositions (no mutual exclusion needed beyond FPC), open markers
(white face, colored edge) for mixed-spin compositions.
"""
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
import uinf_traces_sparse as uts
import plotstyle as ps

ps.apply()

L = 4
N = 16
lam = 1.0
C = ps.C_CONNECTIVITY

cases = [(2, 0), (1, 1), (3, 0), (2, 1), (4, 0), (3, 1), (2, 2)]
shape_by_n = {2: ps.MARKERS[0], 3: ps.MARKERS[1], 4: ps.MARKERS[2]}


def fpc_group(k):
    if k == 0:
        return 0.0
    return 4 * k * lam**2 * (N - k) / (N - 1)


def z_coord(N_):
    return 4  # square lattice coordination number


rows = []
for Nup, Ndown in cases:
    n = Nup + Ndown
    naive = 4 * n * lam**2
    fpc = fpc_group(Nup) + fpc_group(Ndown)
    gutzwiller = lam**2 * n * z_coord(N) * (N - n) / (N - 1)
    H, D = uts.build_Uinf_H_sparse(L, Nup, Ndown)
    mu2, _ = uts.moments_via_traces(H, D)
    single_species = (Nup == 0 or Ndown == 0)
    rows.append(dict(Nup=Nup, Ndown=Ndown, n=n, naive=naive, fpc=fpc,
                      gutzwiller=gutzwiller, exact=mu2, single=single_species))

fig, axes = plt.subplots(1, 3, figsize=(ps.FIGWIDTH_MULTI, 3.3), sharey=True,
                          constrained_layout=True)
lims = (6.5, 17.5)

# Panel (a): naive and exact are BOTH composition-blind at fixed n, so
# every composition at a given n collapses to one point -- plot n=2,3,4
# once each.
ax = axes[0]
ax.plot(lims, lims, color=ps.C_NEUTRAL, lw=1.0, ls=ps.LS_THEORY, zorder=1)
seen_n = {}
for r in rows:
    seen_n.setdefault(r["n"], r)
for n, r in sorted(seen_n.items()):
    ax.scatter(r["naive"], r["exact"], marker=shape_by_n[n], s=75,
               facecolors=C, edgecolors="black", linewidths=1.0, zorder=3)
    ax.annotate(f"$n={n}$", (r["naive"], r["exact"]), textcoords="offset points",
                xytext=(8, -3), fontsize=9, color="0.15")
ax.set_xlim(lims); ax.set_ylim(lims)
ax.set_xlabel(r"$\mu_2^{\rm naive}=4n\lambda^2$")
ax.set_title("independent-particle", fontsize=10.5)
ps.panel_label(ax, "a")
ps.style_axes(ax)

# Panel (b): FPC depends on spin composition -> all 7 points, with
# hand-placed label offsets to avoid overlap among close-lying points.
label_offset = {
    (2, 0): (8, 6), (1, 1): (8, -12),
    (3, 0): (-32, 8), (2, 1): (8, -3),
    (4, 0): (-10, 10), (3, 1): (6, 8), (2, 2): (6, -12),
}
ax = axes[1]
ax.plot(lims, lims, color=ps.C_NEUTRAL, lw=1.0, ls=ps.LS_THEORY, zorder=1)
for r in rows:
    marker = shape_by_n[r["n"]]
    fc = C if r["single"] else "white"
    ax.scatter(r["fpc"], r["exact"], marker=marker, s=68,
               facecolors=fc, edgecolors=C, linewidths=1.2, zorder=3)
    label = f"({r['Nup']},{r['Ndown']})"
    ax.annotate(label, (r["fpc"], r["exact"]), textcoords="offset points",
                xytext=label_offset[(r["Nup"], r["Ndown"])], fontsize=8, color="0.25")
ax.set_xlim(lims); ax.set_ylim(lims)
ax.set_xlabel(r"$\mu_2^{\rm FPC}$")
ax.set_title("same-spin Pauli/FPC", fontsize=10.5)
ps.panel_label(ax, "b")
ps.style_axes(ax)

# Panel (c): full exact U=infinity occupancy (Gutzwiller) correction --
# by construction this is the theorem itself, so every point collapses.
ax = axes[2]
ax.plot(lims, lims, color=ps.C_NEUTRAL, lw=1.0, ls=ps.LS_THEORY, zorder=1)
for r in rows:
    marker = shape_by_n[r["n"]]
    fc = C if r["single"] else "white"
    ax.scatter(r["gutzwiller"], r["exact"], marker=marker, s=68,
               facecolors=fc, edgecolors=C, linewidths=1.2, zorder=3)
ax.set_xlim(lims); ax.set_ylim(lims)
ax.set_xlabel(r"$\mu_2^{\rm Gutzwiller}$")
ax.set_title(r"full $U{=}\infty$ projection", fontsize=10.5)
ps.panel_label(ax, "c")
ps.style_axes(ax)

axes[0].set_ylabel(r"$\mu_2(U\to\infty)$, exact $(\lambda^2)$")

# legend: marker shape = n, fill = single-species vs mixed
legend_elems = [
    Line2D([0], [0], marker=ps.MARKERS[0], color="none", markerfacecolor="0.85",
           markeredgecolor="black", markersize=8, label="$n=2$"),
    Line2D([0], [0], marker=ps.MARKERS[1], color="none", markerfacecolor="0.85",
           markeredgecolor="black", markersize=8, label="$n=3$"),
    Line2D([0], [0], marker=ps.MARKERS[2], color="none", markerfacecolor="0.85",
           markeredgecolor="black", markersize=8, label="$n=4$"),
    Line2D([0], [0], marker="o", color="none", markerfacecolor=C,
           markeredgecolor=C, markersize=8, label="single species"),
    Line2D([0], [0], marker="o", color="none", markerfacecolor="white",
           markeredgecolor=C, markersize=8, label="mixed spin"),
]
fig.legend(handles=legend_elems, loc="outside lower center", ncol=5,
           frameon=False, fontsize=8.5)

fig.savefig("results/naive_vs_fpc_vs_exact.png")
print("wrote results/naive_vs_fpc_vs_exact.png")

for r in rows:
    print(r)
