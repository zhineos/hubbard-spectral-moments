#!/usr/bin/env python3
"""
Numerical validation of the flux-resolved fourth moment mu4(Phi) derived
analytically in analytic_studies/10_flux_resolved_mu4_decomposition.tex.

Builds a genuine Hofstadter (uniform per-plaquette flux) Peierls
Hamiltonian on an LxL periodic torus, projects onto the N_d=0
(no-double-occupancy) sector for two spin species, and computes exact
mu2, mu4 via sparse trace evaluation (never dense diagonalization),
exactly as paper.tex's Appendix E prescribes.

Gauge choice (Landau gauge on a torus): a bulk horizontal hop
(x,y)->(x+1,y) [including the x-wraparound bond, since the phase
depends only on y] carries phase alpha*y, where alpha = 2*pi*p/L^2 is
the (negative of the) flux per elementary plaquette. Bulk vertical hops
carry phase 0. The y-wraparound vertical bond (x,L-1)->(x,0) carries a
compensating phase -alpha*L*x so that every plaquette on the torus,
including every seam and the corner plaquette, encloses exactly the
same flux (mod 2*pi) -- this is mandatory for Dirac-consistent uniform
flux on a topologically nontrivial (boundary-free) surface, and is
verified explicitly below before any physics is computed.
"""
import numpy as np
import matplotlib.pyplot as plt
from itertools import combinations
from scipy.sparse import lil_matrix, csr_matrix

import plotstyle as ps

LAM = 1.0
OUT = "results"


# ================================================================
# 1. Peierls link phases on the LxL torus, uniform flux alpha per
#    plaquette (mod 2*pi), Landau gauge.
# ================================================================

def site_index(x, y, L):
    return x * L + y


def link_phase(x, y, dx, dy, L, alpha):
    """Phase picked up hopping FROM (x,y) in direction (dx,dy) in
    {(1,0),(-1,0),(0,1),(0,-1)}. Landau gauge as described above."""
    if dx == 1:
        return alpha * y
    if dx == -1:
        # reverse of the +x hop from (x-1,y): that hop had phase alpha*y
        return -alpha * y
    if dy == 1:
        if y == L - 1:
            return -alpha * L * x
        return 0.0
    if dy == -1:
        if y == 0:
            # reverse of the wraparound +y hop from (x,L-1)->(x,0),
            # which carried phase -alpha*L*x
            return alpha * L * x
        return 0.0
    raise ValueError("bad direction")


def plaquette_flux(x, y, L, alpha):
    """Sum of directed link phases around the elementary plaquette with
    lower-left corner (x,y): (x,y)->(x+1,y)->(x+1,y+1)->(x,y+1)->(x,y)."""
    xp, yp = (x + 1) % L, (y + 1) % L
    p1 = link_phase(x, y, 1, 0, L, alpha)          # (x,y)->(x+1,y)
    p2 = link_phase(xp, y, 0, 1, L, alpha)         # (x+1,y)->(x+1,y+1)
    p3 = link_phase(xp, yp, -1, 0, L, alpha)       # (x+1,y+1)->(x,y+1)
    p4 = link_phase(x, yp, 0, -1, L, alpha)        # (x,y+1)->(x,y)
    return p1 + p2 + p3 + p4


def validate_uniform_flux(L, p_test_values, verbose=True):
    ok = True
    for p in p_test_values:
        alpha = 2 * np.pi * p / (L * L)
        target = np.exp(-1j * alpha)
        max_err = 0.0
        for x in range(L):
            for y in range(L):
                phi = plaquette_flux(x, y, L, alpha)
                err = abs(np.exp(1j * phi) - target)
                max_err = max(max_err, err)
        passed = max_err < 1e-10
        ok = ok and passed
        if verbose:
            print(f"  L={L} p={p} alpha={alpha:.6f}: "
                  f"max |e^{{i*flux}} - e^{{-i*alpha}}| over all {L*L} "
                  f"plaquettes = {max_err:.3e}  [{'PASS' if passed else 'FAIL'}]")
    return ok


# ================================================================
# 2. Complex sorted-tuple hop with Peierls phase
# ================================================================

def hop_tuple_phase(t, s_from, s_to, L, alpha):
    """Move the fermion at site s_from (must be in tuple t) to s_to.
    Returns (new_sorted_tuple, complex_amplitude_factor) where the
    amplitude factor is (fermion sign) * exp(i * link_phase)."""
    lst = list(t)
    m = lst.index(s_from)
    rest = lst[:m] + lst[m + 1:]
    sign1 = (-1) ** m
    p = sum(1 for v in rest if v < s_to)
    sign2 = (-1) ** p
    new_rest = rest[:p] + [s_to] + rest[p:]

    xf, yf = s_from // L, s_from % L
    xt, yt = s_to // L, s_to % L
    dx = (xt - xf)
    dy = (yt - yf)
    # normalize wraparound displacement to +-1
    if dx == L - 1:
        dx = -1
    elif dx == -(L - 1):
        dx = 1
    if dy == L - 1:
        dy = -1
    elif dy == -(L - 1):
        dy = 1
    phase = link_phase(xf, yf, dx, dy, L, alpha)

    return tuple(new_rest), sign1 * sign2 * np.exp(1j * phase)


def neighbors_of(s, L):
    x, y = s // L, s % L
    return [
        site_index((x + 1) % L, y, L),
        site_index((x - 1) % L, y, L),
        site_index(x, (y + 1) % L, L),
        site_index(x, (y - 1) % L, L),
    ]


# ================================================================
# 3. Two-species N_d=0 projected sector, complex Peierls Hamiltonian
# ================================================================

def build_two_species_basis(L, nup, ndn):
    N = L * L
    basis = []
    index = {}
    up_tuples = list(combinations(range(N), nup)) if nup > 0 else [()]
    for u in up_tuples:
        uset = set(u)
        remaining = [s for s in range(N) if s not in uset]
        if ndn == 0:
            dn_tuples = [()]
        else:
            dn_tuples = list(combinations(remaining, ndn))
        for d in dn_tuples:
            key = (u, d)
            index[key] = len(basis)
            basis.append(key)
    return basis, index


def build_H(L, nup, ndn, lam, alpha):
    basis, index = build_two_species_basis(L, nup, ndn)
    n = len(basis)
    H = lil_matrix((n, n), dtype=complex)
    for (u, d), col in index.items():
        uset, dset = set(u), set(d)
        occupied = uset | dset
        # up-species hops
        for s in u:
            for nb in neighbors_of(s, L):
                if nb in occupied:
                    continue
                new_u, amp = hop_tuple_phase(u, s, nb, L, alpha)
                row = index[(new_u, d)]
                H[row, col] += -lam * amp
        # down-species hops
        for s in d:
            for nb in neighbors_of(s, L):
                if nb in occupied:
                    continue
                new_d, amp = hop_tuple_phase(d, s, nb, L, alpha)
                row = index[(u, new_d)]
                H[row, col] += -lam * amp
    return csr_matrix(H), n


def mu2_mu4_sparse(H, D0):
    H2 = (H @ H).tocsr()
    mu2 = H2.diagonal().sum().real / D0
    mu4 = (np.abs(H2.data) ** 2).sum() / D0
    return mu2, mu4


def check_hermitian(H, tol=1e-10):
    diff = (H - H.conj().T)
    return np.max(np.abs(diff.data)) < tol if diff.nnz else True


def sanity_check_L4():
    print("=" * 70)
    print("Step 1: L=4 zero-flux sanity check vs paper.tex Table (tab:mu4exact)")
    print("=" * 70)
    targets = {
        (2, 0): (7.466667, 145.066667),
        (1, 1): (7.466667, 151.466667),
    }
    all_ok = True
    for (nup, ndn), (mu2_t, mu4_t) in targets.items():
        H, D0 = build_H(4, nup, ndn, LAM, alpha=0.0)
        herm_ok = check_hermitian(H)
        mu2, mu4 = mu2_mu4_sparse(H, D0)
        ok = abs(mu2 - mu2_t) < 1e-5 and abs(mu4 - mu4_t) < 1e-5
        all_ok = all_ok and ok and herm_ok
        print(f"  (Nup,Ndn)=({nup},{ndn}) D0={D0} Hermitian={herm_ok}: "
              f"mu2={mu2:.6f} (target {mu2_t})  mu4={mu4:.6f} (target {mu4_t})  "
              f"[{'PASS' if ok else 'FAIL'}]")
    print(f"  => {'ALL PASS' if all_ok else 'FAILED'}\n")
    return all_ok


def n2_flux_sweep(L, lam=LAM):
    print("=" * 70)
    print(f"Step 2: n=2 flux sweep, L={L} (N={L*L}, {L*L} flux steps)")
    print("=" * 70)
    N = L * L
    ps_list = np.arange(N)
    phis = 2 * np.pi * ps_list / N
    mu4_20 = np.zeros(N)
    mu4_11 = np.zeros(N)
    for i, p in enumerate(ps_list):
        alpha = 2 * np.pi * p / N
        H20, D20 = build_H(L, 2, 0, lam, alpha)
        H11, D11 = build_H(L, 1, 1, lam, alpha)
        _, mu4_20[i] = mu2_mu4_sparse(H20, D20)
        _, mu4_11[i] = mu2_mu4_sparse(H11, D11)

    D = mu4_20 - mu4_11
    D_theory = -64.0 / (N - 1) * lam ** 4 * np.cos(phis)
    resid = D - D_theory
    rms = np.sqrt(np.mean(resid ** 2))
    maxdev = np.max(np.abs(resid))
    print(f"  D(Phi) = mu4^(2,0) - mu4^(1,1); theory = -64/(N-1)*cos(Phi), N={N}")
    print(f"  RMS residual = {rms:.6e}   max |residual| = {maxdev:.6e}")
    print(f"  RMS relative to theory amplitude ({64.0/(N-1):.6f}): "
          f"{rms/(64.0/(N-1)):.3e}\n")
    return phis, mu4_20, mu4_11, D, D_theory, N


def n3_fourier_diagnostic(L, lam=LAM):
    print("=" * 70)
    print(f"Step 3: n=3 diagnostic, L={L} (N={L*L})")
    print("=" * 70)
    N = L * L
    ps_list = np.arange(N)
    phis = 2 * np.pi * ps_list / N
    mu4_30 = np.zeros(N)
    mu4_21 = np.zeros(N)
    for i, p in enumerate(ps_list):
        alpha = 2 * np.pi * p / N
        H30, D30 = build_H(L, 3, 0, lam, alpha)
        H21, D21 = build_H(L, 2, 1, lam, alpha)
        _, mu4_30[i] = mu2_mu4_sparse(H30, D30)
        _, mu4_21[i] = mu2_mu4_sparse(H21, D21)

    # Same-spin-triple minus mixed composition isolates the P_same/P_3
    # dependent exchange piece (both share the identical spin-blind mu2
    # and Type-I/II(a) baseline; only the exchange-sensitive walks --
    # transpositions and, for (3,0) only, genuine 3-cycles -- differ).
    D = mu4_30 - mu4_21

    def dft_cos_component(signal, m, N):
        # exact discrete Fourier projection onto cos(m*phi) on the
        # uniform grid phi_p = 2*pi*p/N
        k = np.arange(N)
        basis = np.cos(m * 2 * np.pi * k / N)
        if m == 0:
            return np.mean(signal)
        return 2.0 * np.mean(signal * basis)

    coeffs = {m: dft_cos_component(D, m, N) for m in range(0, 5)}
    print("  D(Phi) = mu4^(3,0) - mu4^(2,1), cosine DFT coefficients:")
    for m, c in coeffs.items():
        print(f"    cos({m}*Phi): {c:.6e}")
    ratio = abs(coeffs[2]) / abs(coeffs[1]) if coeffs[1] != 0 else float("inf")
    print(f"  |cos(2*Phi)| / |cos(1*Phi)| = {ratio:.3e}")
    verdict = "NUMERICALLY ZERO (pure cos(Phi))" if ratio < 1e-6 else \
        ("negligible" if ratio < 1e-3 else "SIGNIFICANT -- cos(2*Phi) present")
    print(f"  Verdict: {verdict}\n")
    return phis, D, coeffs


def make_figure(phis, D, D_theory, N):
    ps.apply()
    fig, ax = plt.subplots(figsize=(ps.FIGWIDTH_SINGLE, 4.2),
                            constrained_layout=True)
    order = np.argsort(phis)
    ax.plot(phis[order], D[order], "o", color=ps.C_EXCHANGE, ms=4.5,
             mec="white", mew=0.5, zorder=3,
             label=r"Exact: $\mu_4^{(2,0)}(\Phi)-\mu_4^{(1,1)}(\Phi)$")
    phi_fine = np.linspace(0, 2 * np.pi, 400)
    ax.plot(phi_fine, -64.0 / (N - 1) * np.cos(phi_fine),
             color=ps.C_NEUTRAL, lw=1.6, ls=ps.LS_THEORY, zorder=2,
             label=r"Theory: $-\frac{64}{N-1}\cos\Phi$ (no fit)")
    ax.axhline(0, color="0.8", lw=0.6, zorder=1)
    ax.set_xlabel(r"$\Phi$ (flux per plaquette)")
    ax.set_ylabel(r"$\mu_4^{(2,0)}-\mu_4^{(1,1)}\ (\lambda^4)$")
    ax.legend(loc="upper right", frameon=False, fontsize=8.5)
    ps.style_axes(ax)
    fig.savefig(f"{OUT}/mu4_flux_response.png")
    print(f"Saved: {OUT}/mu4_flux_response.png")
    print(f"  Caption should state: n=2, N={N}; exact sparse-trace "
          f"evaluation with a genuine Peierls Hamiltonian, no fitted "
          f"parameters.")


if __name__ == "__main__":
    print("=" * 70)
    print("Step 0: mandatory uniform-flux validation")
    print("=" * 70)
    for L in (4, 5, 6):
        ok = validate_uniform_flux(L, p_test_values=[0, 1, 2, L, L * L - 1])
        print(f"  L={L}: {'ALL PLAQUETTES UNIFORM' if ok else 'FAILED'}\n")

    ok = sanity_check_L4()
    if not ok:
        raise SystemExit("L=4 sanity check failed -- stopping before proceeding.")

    phis, mu4_20, mu4_11, D, D_theory, N = n2_flux_sweep(L=6)
    make_figure(phis, D, D_theory, N)

    # L=4 first: known to carry the L=4-specific wraparound anomalies
    # documented in analytic_studies/06_lattice_specificity_and_finite_size.tex
    # (extra diagonal-type common-neighbor pairs, enhanced edge-channel
    # magnitude) -- included deliberately as a cross-check that those
    # same finite-size pathologies show up here too, not swept aside.
    n3_fourier_diagnostic(L=4)
    # L=5: generic (non-wraparound-pathological) lattice size -- the
    # diagnostic that should be trusted as representative.
    n3_fourier_diagnostic(L=5)
