"""
Schrieffer-Wolff (2nd-order degenerate perturbation theory) correction to
H_infinity = P0 H_t P0, exact through O(1/U).

H = H_t + U*D,  D = number of doubly-occupied sites.
P0 = no-double-occupancy projector (N_d=0 sector); Q1 = exactly-one-doublon
sector (the only sector reachable from P0 by a single hop, so the usual
truncation to virtual states with H_0 eigenvalue U is EXACT here, not an
approximation).

Standard 2nd-order (Schrieffer-Wolff / Rayleigh-Schrodinger) result:
    H_eff = P0 H_t P0 + P0 H_t Q1 (0 - Q1 H_0 Q1)^{-1} Q1 H_t P0 + O(1/U^2)
          = T0 - (1/U) T1^dag T1 + O(1/U^2)
where T0 = P0 H_t P0 (pure hop into an empty site) and
      T1 = Q1 H_t P0 (hop ONTO an opposite-spin occupied site, creating one
      doublon -- the only way a single hop leaves P0).

This module builds T0, T1 as sparse matrices between the P0 basis and the
Q1 (single-doublon) basis, forms V = T1^T @ T1 (real, so T1^dag = T1^T),
and evaluates Tr(T0 V)/D0 (predicted to vanish exactly -- see writeup) and
Tr(V^2)/D0, Tr(V)/D0, which together with the already-known mu2(infinity)
= Tr(T0^2)/D0 give a first-principles prediction for the O(1/U^2)
correction to mu2(U), with NO adjustable parameters.
"""
import numpy as np
from scipy.sparse import lil_matrix, csr_matrix
import sector_theory as st
from three_electron import build_neighbors, LAM


def build_P0_basis(N, Nup, Ndown):
    up_tuples, _ = st.build_ktuple_basis(N, Nup) if Nup > 0 else ([()], {(): 0})
    down_tuples, _ = st.build_ktuple_basis(N, Ndown) if Ndown > 0 else ([()], {(): 0})
    basis = []
    for u in up_tuples:
        uset = set(u)
        for d in down_tuples:
            if uset.isdisjoint(d):
                basis.append((u, d))
    index = {b: i for i, b in enumerate(basis)}
    return basis, index


def build_Q1_basis(N, Nup, Ndown):
    """Exactly one common (doubly-occupied) site between up_tuple and down_tuple."""
    up_tuples, _ = st.build_ktuple_basis(N, Nup) if Nup > 0 else ([()], {(): 0})
    down_tuples, _ = st.build_ktuple_basis(N, Ndown) if Ndown > 0 else ([()], {(): 0})
    basis = []
    for u in up_tuples:
        uset = set(u)
        for d in down_tuples:
            if len(uset.intersection(d)) == 1:
                basis.append((u, d))
    index = {b: i for i, b in enumerate(basis)}
    return basis, index


def build_T0_T1(L, Nup, Ndown, lam=LAM):
    N = L * L
    neighbors = build_neighbors(L)
    p0_basis, p0_index = build_P0_basis(N, Nup, Ndown)
    q1_basis, q1_index = build_Q1_basis(N, Nup, Ndown)
    D0, D1 = len(p0_basis), len(q1_basis)

    T0 = lil_matrix((D0, D0))
    T1 = lil_matrix((D1, D0))

    for (u, d) in p0_basis:
        col = p0_index[(u, d)]
        occ = set(u) | set(d)
        dset = set(d)
        uset = set(u)
        # up electrons hop
        for s in u:
            for nb in neighbors[s]:
                if nb not in occ:
                    new_u, sign = st.hop_ktuple(u, s, nb)
                    row = p0_index[(new_u, d)]
                    T0[row, col] += -lam * sign
                elif nb in dset:  # opposite-spin occupied -> creates doublon
                    new_u, sign = st.hop_ktuple(u, s, nb)
                    row = q1_index[(new_u, d)]
                    T1[row, col] += -lam * sign
        # down electrons hop
        for s in d:
            for nb in neighbors[s]:
                if nb not in occ:
                    new_d, sign = st.hop_ktuple(d, s, nb)
                    row = p0_index[(u, new_d)]
                    T0[row, col] += -lam * sign
                elif nb in uset:
                    new_d, sign = st.hop_ktuple(d, s, nb)
                    row = q1_index[(u, new_d)]
                    T1[row, col] += -lam * sign

    return csr_matrix(T0), csr_matrix(T1), D0, D1


def sw_moments(L, Nup, Ndown, lam=LAM):
    T0, T1, D0, D1 = build_T0_T1(L, Nup, Ndown, lam)
    V = (T1.T @ T1).tocsr()          # D0 x D0, symmetric, = T1^dag T1

    tr_T0sq = (T0.multiply(T0)).sum()        # T0 symmetric -> Tr(T0^2)=sum entries^2
    mu2_inf = tr_T0sq / D0

    tr_T0V = (T0.multiply(V)).sum()          # Tr(T0 V) = sum_ab T0_ab V_ba = sum T0.*V (both symmetric)
    tr_V = V.diagonal().sum()
    tr_Vsq = (V.multiply(V)).sum()

    return dict(D0=D0, D1=D1, mu2_inf=mu2_inf,
                tr_T0V=tr_T0V, tr_V=tr_V, tr_Vsq=tr_Vsq)


if __name__ == "__main__":
    import time
    for L, Nup, Ndown in [(4, 3, 1), (4, 2, 2), (4, 4, 0), (5, 3, 1), (5, 2, 2)]:
        t0 = time.time()
        m = sw_moments(L, Nup, Ndown)
        dt = time.time() - t0
        D0 = m["D0"]
        # H_eff = T0 - V/U ; mu2(U) = mu2_inf - 2*tr_T0V/(D0*U) + (tr_Vsq/D0 - (tr_V/D0)**2)/U**2
        cross_over_D0 = m["tr_T0V"] / D0
        varV = m["tr_Vsq"] / D0 - (m["tr_V"] / D0) ** 2
        print(f"L={L} ({Nup},{Ndown}): D0={D0:6d} D1={m['D1']:6d} "
              f"mu2_inf={m['mu2_inf']:.6f} <T0V>/D0={cross_over_D0:.6e} "
              f"Var(V)={varV:.6f}  predicted 1/U^2 amplitude={varV:.6f}  "
              f"time={dt:.2f}s")
