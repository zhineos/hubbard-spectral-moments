#!/usr/bin/env python3
"""
Fig. 3: the sector-counting rule, tested directly by exact
diagonalization.

(a) n=3 (2 up + 1 down), L=5: E vs N_d at U=10,20,40 lambda -- the
    N_d~1 doublon+electron band separates from the N_d~0 continuum.
(b) n=4 (2 up + 2 down), L=4: the same test, now with three sectors
    N_d=0,1,2, at U=10,20,40 lambda.
(c) n=4, three spin compositions at fixed U=40 lambda: spin
    composition alone controls which N_d sectors are reachable
    (4 up: only N_d=0; 3+1: N_d in {0,1}; 2+2: N_d in {0,1,2}).

Doublon occupation N_d is the organizing variable throughout, so this
figure uses the DOUBLON color family (green shades, darker = more
doublons) rather than an arbitrary per-U or per-composition color
cycle.

Diagonalization strategy: panels (a) and the n=3-like 3+1 sector of
panel (c) use small enough Hamiltonians (dim ~7500-9000) that dense
eigh is fast and light. Panel (b)'s n=4, L=4 sector (dim 14400) is not
-- a full dense eigh there needs several GB and, on a loaded machine,
can trigger severe swap thrashing. Instead we get the N_d=0 and N_d=2
bands via sparse extremal Lanczos (which='SA'/'LA', matrix-vector
products only, no factorization, ~50MB), and the interior N_d=1 band
via exact diagonalization of the projected operator P_1 H P_1
restricted to the (small, ~3360-dimensional) N_d=1 subspace -- the
same "projected operator" logic used throughout this paper, just
applied one moment-order down.
"""
import numpy as np
import matplotlib.pyplot as plt
import gc
from scipy.sparse.linalg import eigsh
import plotstyle as ps

import four_electron as fe
import four_electron_31 as fe31
import three_electron as te

ps.apply()
rng = np.random.default_rng(0)

LAM = 1.0
MAX_PLOT_PTS = 4000


def subsample(E, Nd, maxpts=MAX_PLOT_PTS):
    if len(E) <= maxpts:
        return E, Nd
    idx = rng.choice(len(E), size=maxpts, replace=False)
    return E[idx], Nd[idx]


def eps_d(U, lam=LAM):
    return U + 8 * lam**2 / U


def dense_eigh(H):
    Hd = H.toarray()
    w, v = np.linalg.eigh(Hd)
    del Hd
    gc.collect()
    return w, v


def four_electron_spectrum(L, U, k_extremal=300):
    """N_d=0 and N_d=2 bands via extremal Lanczos; N_d=1 band via
    exact diagonalization of the projected operator on the small
    N_d=1 subspace. Returns concatenated (E, N_d) arrays."""
    H, indicator, pairs, index, N = fe.build_four_electron_H(L, U)

    w0, v0 = eigsh(H, k=k_extremal, which="SA")
    Nd0 = fe.n_d_expectation(v0, indicator)

    w2, v2 = eigsh(H, k=k_extremal, which="LA")
    Nd2 = fe.n_d_expectation(v2, indicator)
    clean2 = Nd2 > 1.5
    w2, Nd2 = w2[clean2], Nd2[clean2]

    idx1 = np.where(np.abs(indicator - 1.0) < 0.5)[0]
    H1 = H[idx1][:, idx1].toarray()
    w1 = np.linalg.eigvalsh(H1)
    Nd1 = np.ones_like(w1)
    del H, H1
    gc.collect()

    return (np.concatenate([w0, w1, w2]),
            np.concatenate([Nd0, Nd1, Nd2]))


MARKER_BY_U = {10.0: "o", 20.0: "s", 40.0: "^"}
CMAP_DOUBLON = ps.doublon_cmap()


def sector_mean(w, Nd, k):
    mask = np.abs(Nd - k) < 0.5
    return w[mask].mean(), mask.sum()


def plot_panel(ax, U_values, per_U, sector_ks, sector_preds, x_of_k):
    """Shared rendering: faint true-Nd cloud (color = continuous <N_d>,
    marker shape = U) + strong sector-mean markers + short reference
    dashes at the predicted energy. No jitter: the plotted x is always
    the actual (possibly non-integer) <N_d> expectation value."""
    for U in U_values:
        w, Nd = per_U[U]
        w_s, Nd_s = subsample(w, Nd)
        ax.scatter(Nd_s, w_s, c=Nd_s, cmap=CMAP_DOUBLON, vmin=0,
                   vmax=max(sector_ks), s=4, alpha=0.35, linewidths=0,
                   marker=MARKER_BY_U[U], zorder=2)

    for U in U_values:
        w, Nd = per_U[U]
        for k in sector_ks:
            mean_E, count = sector_mean(w, Nd, k)
            pred = sector_preds[k](U)
            x0 = x_of_k(k)
            ax.plot([x0 - 0.18, x0 + 0.18], [pred, pred], color="0.35",
                    lw=1.3, ls=(0, (1, 1)), zorder=3)
            ax.scatter([x0], [mean_E], marker=MARKER_BY_U[U], s=70,
                       color=CMAP_DOUBLON(k / max(sector_ks) if max(sector_ks) else 0),
                       edgecolors="black", linewidths=0.9, zorder=4)

    handles = [plt.Line2D([0], [0], marker=MARKER_BY_U[U], color="none",
                           markerfacecolor="0.6", markeredgecolor="black",
                           markersize=7, label=rf"$U={U:g}\lambda$")
               for U in U_values]
    handles.append(plt.Line2D([0], [0], color="0.35", lw=1.3, ls=(0, (1, 1)),
                               label=r"predicted sector center"))
    return handles


# ------------------------------------------------------------------
# panel (a): n=3, 2 up + 1 down, L=5
# ------------------------------------------------------------------
def panel_a(ax):
    L = 5
    U_values = [10.0, 20.0, 40.0]
    per_U = {}
    for U in U_values:
        H, indicator, pairs, index, N = te.build_three_electron_H(L, U)
        w, v = dense_eigh(H)
        Nd = te.n_d_expectation(v, indicator)
        per_U[U] = (w, Nd)
        mean_E, count = sector_mean(w, Nd, 1)
        print(f"  (a) U={U:g}: N_d~1 band mean={mean_E:.4f} (n={count}), "
              f"predicted eps_d={eps_d(U):.4f}", flush=True)

    handles = plot_panel(ax, U_values, per_U, sector_ks=[0, 1],
                          sector_preds={0: lambda U: 0.0, 1: eps_d},
                          x_of_k=lambda k: k)

    ax.set_xticks([0, 1])
    ax.set_xlim(-0.35, 1.35)
    ax.set_xlabel(r"$\langle N_d\rangle$")
    ax.set_ylabel(r"$E\ (\lambda)$")
    ps.panel_label(ax, "a", loc="lower right")
    ax.legend(handles=handles, fontsize=7.5, loc="upper left")
    ps.style_axes(ax)


# ------------------------------------------------------------------
# panel (b): n=4, 2 up + 2 down, L=4
# ------------------------------------------------------------------
def panel_b(ax, cache):
    L = 4
    U_values = [10.0, 20.0, 40.0]
    per_U = {}

    for U in U_values:
        if U in cache:
            w, Nd = cache[U]
        else:
            w, Nd = four_electron_spectrum(L, U)
            cache[U] = (w, Nd)
        per_U[U] = (w, Nd)
        mean_E, count = sector_mean(w, Nd, 2)
        print(f"  (b) U={U:g}: N_d~2 band mean={mean_E:.4f} (n={count}), "
              f"predicted 2*eps_d={2*eps_d(U):.4f}", flush=True)

    handles = plot_panel(ax, U_values, per_U, sector_ks=[0, 1, 2],
                          sector_preds={0: lambda U: 0.0, 1: eps_d,
                                        2: lambda U: 2 * eps_d(U)},
                          x_of_k=lambda k: k)

    ax.set_xticks([0, 1, 2])
    ax.set_xlim(-0.35, 2.35)
    ax.set_xlabel(r"$\langle N_d\rangle$")
    ps.panel_label(ax, "b", loc="lower right")
    ax.legend(handles=handles, fontsize=7.5, loc="upper left")
    ps.style_axes(ax)


# ------------------------------------------------------------------
# panel (c): n=4, three spin compositions, fixed U=40
# ------------------------------------------------------------------
def panel_c(ax, cache):
    L = 4
    U = 40.0
    compositions = [("$(4,0)$", "4,0"), ("$(3,1)$", "3,1"), ("$(2,2)$", "2,2")]
    # same continuous colormap as panels (a,b): color = <N_d>/2
    doublon_color = [CMAP_DOUBLON(k / 2) for k in range(3)]

    # 4 up (no interaction possible: single species, U=0 combinatorics
    # via the tight-binding spectrum -- exact, no diagonalization)
    from three_electron import build_neighbors, adjacency_matrix
    neighbors = build_neighbors(L)
    A = adjacency_matrix(L, neighbors, LAM).toarray()
    eps = np.linalg.eigvalsh(A)
    N = L * L
    combos = rng.choice(N, size=(MAX_PLOT_PTS, 4), replace=True)
    combos = np.sort(combos, axis=1)
    valid = np.all(np.diff(combos, axis=1) > 0, axis=1)
    combos = combos[valid][:MAX_PLOT_PTS]
    E_4up = eps[combos].sum(axis=1)
    Nd_4up = np.zeros(len(E_4up))

    # 3+1 at U=40 (small dense diag, reuse cache if available)
    key31 = ("31", U)
    if key31 in cache:
        w31, Nd31 = cache[key31]
    else:
        H, indicator, tuples, N_ = fe31.build_H_31(L, U)
        w31, v = dense_eigh(H)
        Nd31 = fe31.n_d_expectation(v, indicator)
        cache[key31] = (w31, Nd31)
        del v
        gc.collect()

    # 2+2 at U=40: reuse panel (b)'s cache directly
    w22, Nd22 = cache[U]

    datasets = [(E_4up, Nd_4up), subsample(w31, Nd31), subsample(w22, Nd22)]

    for i, (label, _) in enumerate(compositions):
        E, Nd = datasets[i]
        for nd_val in sorted(set(np.round(Nd).astype(int))):
            mask = np.abs(Nd - nd_val) < 0.5
            xj = i + (rng.random(mask.sum()) - 0.5) * 0.32
            ax.scatter(xj, E[mask], s=3, color=doublon_color[nd_val],
                       alpha=0.55, linewidths=0)

    ax.set_xticks([0, 1, 2])
    ax.set_xticklabels([c[0] for c in compositions])
    ax.set_xlim(-0.5, 2.5)
    ax.set_xlabel(r"$(N_\uparrow,N_\downarrow)$")
    ps.panel_label(ax, "c", loc="lower right")

    from matplotlib.lines import Line2D
    handles = [Line2D([0], [0], marker="o", color="none",
                       markerfacecolor=doublon_color[k], markersize=7,
                       label=rf"$N_d={k}$") for k in range(3)]
    ax.legend(handles=handles, fontsize=8, loc="upper left")
    ps.style_axes(ax)


if __name__ == "__main__":
    fig, axes = plt.subplots(1, 3, figsize=(ps.FIGWIDTH_MULTI, 3.6),
                              constrained_layout=True)
    cache_b = {}
    print("Panel (a): n=3, L=5 ...", flush=True)
    panel_a(axes[0])
    print("Panel (b): n=4, L=4 ...", flush=True)
    panel_b(axes[1], cache_b)
    print("Panel (c): n=4 spin compositions, L=4, U=40 ...", flush=True)
    panel_c(axes[2], cache_b)

    fig.savefig("results/fig_sectors.png")
    print("wrote results/fig_sectors.png", flush=True)
