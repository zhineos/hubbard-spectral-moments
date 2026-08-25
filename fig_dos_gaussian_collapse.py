#!/usr/bin/env python3
"""
Fig. (Appendix A): instead of showing that the high-d DOS curves look
alike, quantify HOW alike via variance-normalized collapse onto the
unit Gaussian and the residual, plus the exact excess-kurtosis law
gamma_2(d) = -3/(2d).

This is background/methods material for the connectivity (mu_2) story
of Sec. V, so dimension d -- an ordered parameter -- is rendered with a
sequential CONNECTIVITY-family colormap rather than an arbitrary
categorical cycle; the Gaussian reference curve stays neutral black,
dashed, per the manuscript-wide convention.
"""
import numpy as np
import matplotlib.pyplot as plt
from scipy.special import jv, ellipk
from scipy.integrate import quad
import plotstyle as ps

ps.apply()

LAM = 1.0


def rho_1d_exact(E, lam=LAM):
    E = np.atleast_1d(np.asarray(E, dtype=float))
    out = np.zeros_like(E)
    inside = np.abs(E) < 2 * lam
    out[inside] = 1.0 / (np.pi * np.sqrt((2 * lam) ** 2 - E[inside] ** 2))
    return out


def rho_2d_exact(E, lam=LAM):
    E = np.atleast_1d(np.asarray(E, dtype=float))
    out = np.zeros_like(E)
    inside = np.abs(E) < 4 * lam
    m = 1 - (E[inside] / (4 * lam)) ** 2
    out[inside] = ellipk(m) / (2 * np.pi**2 * lam)
    return out


def rho_bessel(E, d, lam=LAM, Tmax=500.0, limit=2000):
    def integrand(t):
        return jv(0, 2 * lam * t) ** d
    E = np.atleast_1d(np.asarray(E, dtype=float))
    out = np.zeros_like(E)
    edge = 2 * d * lam
    for i, e in enumerate(E):
        if abs(e) >= edge:
            out[i] = 0.0
            continue
        val, _ = quad(integrand, 0, Tmax, weight="cos", wvar=e, limit=limit)
        out[i] = val / np.pi
    out[np.abs(out) < 1e-6] = 0.0
    return out


def rho_any(E, d, lam=LAM):
    if d == 1:
        return rho_1d_exact(E, lam)
    if d == 2:
        return rho_2d_exact(E, lam)
    return rho_bessel(E, d, lam)


fig, axes = plt.subplots(1, 3, figsize=(ps.FIGWIDTH_MULTI, 3.9),
                          constrained_layout=True)

low_d = [1, 2, 3, 4]
high_d = [4, 5, 6, 8]
colors_low = ps.connectivity_shades(len(low_d))
colors_high = ps.connectivity_shades(len(high_d))

# --- panel (a): low-d raw DOS, van Hove structure disappearing ---
ax = axes[0]
Es = np.linspace(-8.2, 8.2, 900)
for d, c in zip(low_d, colors_low):
    rho = rho_any(Es, d)
    ax.plot(Es, rho, lw=1.5, color=c, label=f"$d={d}$")
ax.set_xlabel(r"$E/\lambda$")
ax.set_ylabel(r"$\rho_d(E)$")
ax.set_title("Low-dimensional DOS", fontsize=10.5)
ps.panel_label(ax, "a")
a_handles, a_labels = ax.get_legend_handles_labels()
ax.set_xlim(-8.2, 8.2)
ps.style_axes(ax)

# --- panel (b): variance-normalized collapse, d=4,5,6,8, vs Gaussian ---
ax = axes[1]
xs = np.linspace(-4.2, 4.2, 700)
curves = {}
for d, c in zip(high_d, colors_high):
    sigma = np.sqrt(2 * d) * LAM  # sqrt(mu2), mu2 = 2 d lambda^2
    E = xs * sigma
    rho = rho_bessel(E, d)
    rho_tilde = sigma * rho  # normalize so integral over x is 1
    curves[d] = rho_tilde
    ax.plot(xs, rho_tilde, lw=1.4, color=c, label=f"$d={d}$")
g = np.exp(-xs**2 / 2) / np.sqrt(2 * np.pi)
ax.plot(xs, g, color=ps.C_NEUTRAL, ls=ps.LS_THEORY, lw=1.6, label="Gaussian")
ax.set_xlabel(r"$x=E/\sqrt{\mu_2}$")
ax.set_ylabel(r"$\tilde\rho_d(x)$")
ax.set_title("Variance-normalized DOS", fontsize=10.5)
ps.panel_label(ax, "b")
b_handles, b_labels = ax.get_legend_handles_labels()
ps.style_axes(ax)

# --- panel (c): residual from Gaussian ---
ax = axes[2]
for d, c in zip(high_d, colors_high):
    ax.plot(xs, curves[d] - g, lw=1.4, color=c, label=f"$d={d}$")
ax.axhline(0, color=ps.C_NEUTRAL, ls=ps.LS_THEORY, lw=1.0)
ax.set_xlabel(r"$x=E/\sqrt{\mu_2}$")
ax.set_ylabel(r"$\tilde\rho_d(x)-g(x)$")
ax.set_title("Deviation from Gaussian", fontsize=10.5)
ps.panel_label(ax, "c")
ps.style_axes(ax)

# Two compact horizontal legends, one per group of panels that actually
# share a d-family (a alone: d=1,2,3,4; b+c together: d=4,5,6,8+Gaussian)
# rather than one legend trying to cover curves absent from some panels,
# and rather than per-panel legends crammed inside the data region. Both
# use fig.legend() in the SAME (figure-fraction) coordinate system so
# they align on one horizontal band; axes positions are queried only
# after a draw pass, since constrained_layout finalizes them at render
# time, not at the point subplots() returns.
fig.canvas.draw()
pos_a = axes[0].get_position()
pos_b = axes[1].get_position()
pos_c = axes[2].get_position()
y_anchor = max(pos_a.y1, pos_b.y1, pos_c.y1) + 0.02

fig.legend(a_handles, a_labels, loc="lower center",
           bbox_to_anchor=(0.5 * (pos_a.x0 + pos_a.x1), y_anchor),
           ncol=len(a_handles), frameon=False, fontsize=8,
           handlelength=1.4, columnspacing=1.2)
fig.legend(b_handles, b_labels, loc="lower center",
           bbox_to_anchor=(0.5 * (pos_b.x0 + pos_c.x1), y_anchor),
           ncol=len(b_handles), frameon=False, fontsize=8,
           handlelength=1.4, columnspacing=1.2)

fig.savefig("results/dos_gaussian_collapse.png")
print("wrote results/dos_gaussian_collapse.png")

# sanity print of the residual amplitude and the kurtosis law
for d in high_d:
    gamma2 = -3 / (2 * d)
    max_resid = np.max(np.abs(curves[d] - g))
    print(f"d={d}: gamma_2={gamma2:.4f}  max|residual|={max_resid:.4f}")
