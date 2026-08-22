#!/usr/bin/env python3
"""
Reproduction of Fig. 3 of Souza & Claro (2010), arXiv:1005.1857.

Time evolution of the average ("centroid") position of two interacting
electrons on a 9x9 (N=81 site) lattice under an electric field, solved
with a unitary Crank-Nicolson propagator (Eq. 3), followed by a Fourier
(power) spectrum of the resulting oscillation (Eq. 6 + FFT).

IMPORTANT convention note (bug fixed relative to the first-generation
remake, old/remake_2026/test.py): the paper's frequencies (F, 2F, U+-F)
are ANGULAR frequencies (hbar=1, E and omega share units of lambda).
np.fft.rfftfreq returns ordinary frequency (cycles per unit time); it must
be multiplied by 2*pi before comparing against F, 2F, U+-F, otherwise the
reference lines land at the wrong place relative to the actual FFT peaks.
"""

import numpy as np
import matplotlib.pyplot as plt

from scipy.sparse import lil_matrix, identity
from scipy.sparse.linalg import splu

L = 9
N = L ** 4
LAM = 1.0
F = 10.0
U_VALUES = [0.0, 100.0]

dt = 0.002
T = 40.0
NSTEPS = int(T / dt)
SAMPLE_EVERY = 5

OUT = "results"


def index(x1, y1, x2, y2):
    return (((x1 * L) + y1) * L + x2) * L + y2


def coordinates(p):
    y2 = p % L
    p //= L
    x2 = p % L
    p //= L
    y1 = p % L
    p //= L
    x1 = p
    return x1, y1, x2, y2


def build_hamiltonian(U):
    H = lil_matrix((N, N), dtype=np.complex128)

    for x1 in range(L):
        for y1 in range(L):
            for x2 in range(L):
                for y2 in range(L):
                    p = index(x1, y1, x2, y2)

                    field = F * (x1 + y1 + x2 + y2)
                    interaction = U if (x1 == x2 and y1 == y2) else 0.0
                    H[p, p] = field + interaction

                    for xx, yy in [(x1 - 1, y1), (x1 + 1, y1),
                                   (x1, y1 - 1), (x1, y1 + 1)]:
                        if 0 <= xx < L and 0 <= yy < L:
                            H[p, index(xx, yy, x2, y2)] += -LAM

                    for xx, yy in [(x2 - 1, y2), (x2 + 1, y2),
                                   (x2, y2 - 1), (x2, y2 + 1)]:
                        if 0 <= xx < L and 0 <= yy < L:
                            H[p, index(x1, y1, xx, yy)] += -LAM

    return H.tocsc()


def initial_state():
    """
    Paper's initial condition: unit amplitude at (x1,y1,x2,y2)=(r,s,r,s)
    for r,s = 4,5,6 (on the interaction hyperplane), plus a few nearby
    points when r != s and either r or s = 5.
    """
    psi = np.zeros(N, dtype=np.complex128)
    points = set()

    for r in (4, 5, 6):
        for s in (4, 5, 6):
            points.add((r, s, r, s))
            if r != s and (r == 5 or s == 5):
                for xx, yy in [(r + 1, s), (r - 1, s), (r, s + 1), (r, s - 1)]:
                    if 0 <= xx < L and 0 <= yy < L:
                        points.add((r, s, xx, yy))

    for pnt in points:
        psi[index(*pnt)] = 1.0
    psi /= np.linalg.norm(psi)

    print("Initial-state configurations:", len(points))
    return psi


def evolve(H, psi0):
    I = identity(N, format="csc", dtype=np.complex128)
    A = I + 0.5j * dt * H
    B = I - 0.5j * dt * H
    solver = splu(A)

    psi = psi0.copy()

    x1_arr = np.zeros(N)
    for p in range(N):
        x1, y1, x2, y2 = coordinates(p)
        x1_arr[p] = x1

    times = np.zeros(NSTEPS // SAMPLE_EVERY + 1)
    rx1 = np.zeros_like(times)

    k = 0
    for step in range(NSTEPS + 1):
        if step % SAMPLE_EVERY == 0:
            prob = np.abs(psi) ** 2
            times[k] = step * dt
            rx1[k] = np.sum(prob * x1_arr)
            k += 1
        if step == NSTEPS:
            break
        psi = solver.solve(B @ psi)

    return times, rx1


def spectrum(t, signal, skip=2.0):
    """
    Drop the initial transient (the sudden switch-on of the localized
    initial packet at t=0 is not periodic and otherwise leaks broadband
    low-frequency power into the FFT, swamping the genuine F/2F/U+-F
    lines) before windowing and transforming.
    """
    mask = t >= skip
    t, signal = t[mask], signal[mask]

    signal = signal - np.mean(signal)
    window = np.hanning(len(signal))
    y = signal * window

    fft = np.fft.rfft(y)
    freq_ordinary = np.fft.rfftfreq(len(y), d=t[1] - t[0])
    freq_angular = 2.0 * np.pi * freq_ordinary   # <-- the earlier fix
    power = np.abs(fft) ** 2

    return freq_angular, power


def run(U):
    print()
    print("=" * 60)
    print(f"Running U = {U:g}")
    print("=" * 60)

    H = build_hamiltonian(U)
    print("Hamiltonian dimension:", H.shape, "nonzeros:", H.nnz)

    psi0 = initial_state()

    print("Propagating (Crank-Nicolson, unitary)...")
    t, rx1 = evolve(H, psi0)

    freq, power = spectrum(t, rx1)

    np.savetxt(
        f"{OUT}/position_U{U:g}.dat",
        np.column_stack((t, rx1)),
        header="t Rx1"
    )
    np.savetxt(
        f"{OUT}/spectrum_U{U:g}.dat",
        np.column_stack((freq, power)),
        header="angular_frequency(lambda) power"
    )

    # report dominant peaks for sanity-checking against F, 2F, U+-F
    mask = freq > 0.5
    order = np.argsort(-power[mask])[:5]
    print("Dominant angular-frequency peaks (lambda):")
    for f, p in zip(freq[mask][order], power[mask][order]):
        print(f"    omega = {f:7.3f}   power = {p:.4g}")

    return t, rx1, freq, power


def main():
    results = {U: run(U) for U in U_VALUES}

    fig, axes = plt.subplots(2, 1, figsize=(9, 8))

    for ax, U in zip(axes, U_VALUES):
        t, rx1, freq, power = results[U]

        ax.plot(freq, power, color="black", lw=1)
        ax.axvline(F, color="tab:blue", ls="--", alpha=0.7, label="F")

        if U > 0:
            ax.axvline(2 * F, color="tab:red", ls="--", alpha=0.7, label="2F")
            ax.axvline(U - F, color="tab:green", ls=":", alpha=0.7, label="U-F")
            ax.axvline(U + F, color="tab:purple", ls=":", alpha=0.7, label="U+F")
            ax.set_xlim(0, U + F + 30)

            # A slow (omega < 2) secular drift -- leakage from residual
            # overlap with nearby extended (B-band) states in the initial
            # packet -- dominates raw power but isn't part of the F/2F/U+-F
            # physics under test, so scale the y-axis to the physically
            # relevant window instead of letting it swamp the plot.
            physical = freq > 3.0
            ax.set_ylim(0, 1.15 * power[physical].max())

            # inset near the interaction-induced sidebands, echoing the
            # paper's Fig. 3 inset
            inset = ax.inset_axes([0.62, 0.35, 0.35, 0.55])
            mask = (freq > U - F - 15) & (freq < U + F + 15)
            inset.plot(freq[mask], power[mask], color="black", lw=1)
            inset.axvline(U - F, color="tab:green", ls=":", alpha=0.7)
            inset.axvline(U + F, color="tab:purple", ls=":", alpha=0.7)
            inset.set_title("near U±F", fontsize=8)
            inset.tick_params(labelsize=7)
        else:
            ax.set_xlim(0, 4 * F)

        ax.set_ylabel(r"$\overline{R}_1(\omega)$")
        ax.set_title(f"U = {U:g}$\\lambda$, F = {F:g}$\\lambda$")
        ax.legend(loc="upper left", fontsize=8)

    axes[-1].set_xlabel(r"Angular frequency $\omega$ ($\lambda$)")
    fig.suptitle(
        "Reproduction of Fig. 3 — Souza & Claro (2010)\n"
        "9x9 lattice (N=81), electric field F=10$\\lambda$",
        fontsize=11
    )
    fig.tight_layout(rect=[0, 0, 1, 0.93])

    filename = f"{OUT}/fig3_centroid_reproduction.png"
    fig.savefig(filename, dpi=200)
    print(f"\nSaved: {filename}")


if __name__ == "__main__":
    main()
