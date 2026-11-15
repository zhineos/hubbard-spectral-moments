"""
Schrieffer-Wolff (degenerate perturbation theory) expansion of the N_d = 0 band of
H = H_t + U*D, through O(1/U^2).

D = number of doubly-occupied sites. P0 = no-double-occupancy projector (N_d=0 sector);
Q1 = exactly-one-doublon sector. A single hop from P0 reaches only Q1, and a path
P0 -> Q1 -> Q1 -> P0 cannot pass through Q2, so through third order only Q1 appears:

    H_eff = T0 - V/U + H3/U^2 + O(1/U^3),
    T0  = P0 H_t P0            (hop into an empty site)
    T1  = Q1 H_t P0            (hop onto an opposite-spin occupied site: creates the doublon)
    T0Q = Q1 H_t Q1            (hop that keeps exactly one doublon)
    V   = T1^T T1
    H3  = T1^T T0Q T1 - (V T0 + T0 V)/2

Because Tr T0 = 0, the central second moment of the band is

    mu2c(U) = mu2(inf) - 2 Tr(T0 V)/(D0 U) + c2/U^2 + O(1/U^3),
    c2 = Var(V) + 2 Tr(T0 H3)/D0,   Var(V) = Tr V^2/D0 - (Tr V/D0)^2,
    Tr(T0 H3) = Tr(T0 T1^T T0Q T1) - Tr(T0^2 V).

Tr(T0 V) = 0 on triangle-free graphs (L >= 4 tori). At lambda = 1 every trace is an
integer, so c2 is an exact rational. checks/run_checks.py compares c2 with exact
diagonalization of the full Hubbard model.
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


def build_T0Q(L, Nup, Ndown, lam=LAM):
    """Q1 H_t Q1: hops from a one-doublon state that leave exactly one doublon (a single
    electron hopping into an empty site, or a doublon electron hopping onto an
    opposite-spin singly occupied site, which moves the doublon)."""
    N = L * L
    neighbors = build_neighbors(L)
    q1_basis, q1_index = build_Q1_basis(N, Nup, Ndown)
    D1 = len(q1_basis)
    T0Q = lil_matrix((D1, D1))
    for (u, d) in q1_basis:
        col = q1_index[(u, d)]
        uset, dset = set(u), set(d)
        for s in u:
            for nb in neighbors[s]:
                if nb in uset:
                    continue
                new_u, sign = st.hop_ktuple(u, s, nb)
                if len(set(new_u) & dset) == 1:
                    T0Q[q1_index[(new_u, d)], col] += -lam * sign
        for s in d:
            for nb in neighbors[s]:
                if nb in dset:
                    continue
                new_d, sign = st.hop_ktuple(d, s, nb)
                if len(uset & set(new_d)) == 1:
                    T0Q[q1_index[(u, new_d)], col] += -lam * sign
    return csr_matrix(T0Q)


def sw_moments(L, Nup, Ndown, lam=LAM, third_order=False):
    T0, T1, D0, D1 = build_T0_T1(L, Nup, Ndown, lam)
    V = (T1.T @ T1).tocsr()          # D0 x D0, symmetric, = T1^dag T1

    tr_T0sq = (T0.multiply(T0)).sum()        # T0 symmetric -> Tr(T0^2)=sum entries^2
    mu2_inf = tr_T0sq / D0

    tr_T0V = (T0.multiply(V)).sum()          # Tr(T0 V) = sum_ab T0_ab V_ba = sum T0.*V (both symmetric)
    tr_V = V.diagonal().sum()
    tr_Vsq = (V.multiply(V)).sum()

    out = dict(D0=D0, D1=D1, mu2_inf=mu2_inf, tr_T0V=tr_T0V, tr_V=tr_V, tr_Vsq=tr_Vsq)
    if third_order:
        T0Q = build_T0Q(L, Nup, Ndown, lam)
        A = (T1 @ T0 @ T1.T).tocsr()                      # D1 x D1
        out["tr_T0H3"] = (T0Q.multiply(A.T)).sum() - ((T0 @ T0).multiply(V)).sum()
    return out


if __name__ == "__main__":
    import time
    for L, Nup, Ndown in [(4, 3, 1), (4, 2, 2), (4, 4, 0), (5, 3, 1), (5, 2, 2)]:
        t0 = time.time()
        m = sw_moments(L, Nup, Ndown, third_order=True)
        D0 = m["D0"]
        varV = m["tr_Vsq"] / D0 - (m["tr_V"] / D0) ** 2
        c2 = varV + 2 * m["tr_T0H3"] / D0
        print(f"L={L} ({Nup},{Ndown}): D0={D0:6d} D1={m['D1']:6d} mu2_inf={m['mu2_inf']:.6f} "
              f"Tr(T0 V)/D0={m['tr_T0V'] / D0:.1e} Var(V)={varV:.6f} c2={c2:.6f}  "
              f"time={time.time() - t0:.2f}s")
