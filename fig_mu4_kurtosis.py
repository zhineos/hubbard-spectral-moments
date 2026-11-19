#!/usr/bin/env python3
"""
Fig. (fig:mu4kurtosis): excess kurtosis of the U = infinity configuration-graph spectrum against
filling, from the closed form mu4 = A(N, n) + alpha(N, n) P_same (mu4_closed_form.py) and the
second-moment theorem, on L x L square tori.

(a) Particle statistics at L = 32: hard-core bosons (no exchange signs), projected fermions with
    N_up = ceil(n/2), and a single spin species. At fixed filling the excess kurtosis is of order
    1/N, so N*gamma2 is plotted; the boson curve is compared with its large-N limit
    5/2 - 3/[4 nu (1 - nu)] (L >= 5 square tori: m = 2N, W = 6N, C4 = N).
(b) Size convergence for N_up = ceil(n/2), L = 5, 8, 16, 32, with exact sparse traces at L = 5,
    n = 2, 3, 4 (uinf_traces_sparse.py) as open circles.

mu4 measures exchange, so the fermion curves use the EXCHANGE color family; the bosons, which
carry no exchange signs, use CONNECTIVITY.
"""
from fractions import Fraction

import matplotlib.pyplot as plt
import numpy as np

import mu4_closed_form as m4c
import plotstyle as ps
from uinf_traces_sparse import build_Uinf_H_sparse

ps.apply()


def torus(L):
    nb = []
    for x in range(L):
        for y in range(L):
            nb.append(sorted({((x + 1) % L) * L + y, ((x - 1) % L) * L + y,
                              x * L + (y + 1) % L, x * L + (y - 1) % L}))
    return nb


def scaled_kurtosis(L, kind):
    nb = torus(L)
    inv = m4c.invariants(nb)
    N = L * L
    nu, y = [], []
    for n in range(1, N):
        m2 = m4c.mu2(nb, n, inv)
        if kind == "boson":
            m4 = m4c.mu4_hcb(nb, n, inv)
        elif kind == "balanced":
            m4 = m4c.mu4_fermion(nb, (n + 1) // 2, n // 2, inv)
        else:
            m4 = m4c.mu4_fermion(nb, n, 0, inv)
        nu.append(n / N)
        y.append(float(N * (m4 / m2 ** 2 - 3)))
    return np.array(nu), np.array(y)


fig, axs = plt.subplots(1, 2, figsize=(9.6, 3.9), sharey=True)
ax = axs[0]
for kind, lab, col, ls in (("boson", "hard-core bosons", ps.C_CONNECTIVITY, "-"),
                           ("balanced", r"fermions, $N_\uparrow=\lceil n/2\rceil$", ps.C_EXCHANGE, "-"),
                           ("polarized", "fermions, one species", ps.C_EXCHANGE, "-.")):
    nu, y = scaled_kurtosis(32, kind)
    ax.plot(nu, y, color=col, ls=ls, lw=1.8, label=lab)
q = np.linspace(0.02, 0.98, 400)
ax.plot(q, 2.5 - 0.75 / (q * (1 - q)), color=ps.C_NEUTRAL, ls=ps.LS_THEORY, lw=1.2,
        label=r"bosons, $N\to\infty$: $\frac{5}{2}-\frac{3}{4\nu(1-\nu)}$")
ax.set_title(r"(a) particle statistics, $L=32$", fontsize=10)
ax.legend(fontsize=8, loc="lower center")

ax = axs[1]
shades = ps.exchange_shades(4)[::-1]   # palest = smallest L, darkest = largest
for L, col in zip((5, 8, 16, 32), shades):
    nu, y = scaled_kurtosis(L, "balanced")
    ax.plot(nu, y, color=col, lw=1.8, label=f"$L={L}$")
for n in (2, 3, 4):
    a, b = (n + 1) // 2, n // 2
    H, D = build_Uinf_H_sparse(5, a, b, lam=1.0)
    H2 = H @ H
    mu2 = Fraction(int(round(H2.diagonal().sum())), D)
    mu4 = Fraction(int(round(H2.multiply(H2).sum())), D)
    assert mu4 == m4c.mu4_fermion(torus(5), a, b)
    ax.plot(n / 25, float(25 * (mu4 / mu2 ** 2 - 3)), ls="none", marker="o", ms=7, mfc="white",
            mec=ps.C_NEUTRAL, mew=1.4, label="exact trace, $L=5$" if n == 2 else None)
ax.set_title(r"(b) size convergence, $N_\uparrow=\lceil n/2\rceil$", fontsize=10)
ax.legend(fontsize=8, loc="lower center", ncol=2)
for ax in axs:
    ax.axhline(0, color=ps.C_NEUTRAL, lw=0.8)
    ax.set_xlim(0, 1)
    ax.set_ylim(-14, 1.5)
    ax.set_xlabel(r"filling $\nu=n/N$")
    ps.style_axes(ax)
axs[0].set_ylabel(r"$N\gamma_2=N(\mu_4/\mu_2^2-3)$")
fig.tight_layout()
fig.savefig("results/mu4_kurtosis.png")
print("wrote results/mu4_kurtosis.png")
