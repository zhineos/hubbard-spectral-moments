"""Exact Tr(H^2)/D and Tr(H^4)/D for P0 H_t P0 via sparse matrix
products -- no diagonalization needed."""
import numpy as np
from scipy.sparse import lil_matrix, csr_matrix
import sector_theory as st
from three_electron import build_neighbors, LAM

def build_Uinf_H_sparse(L, Nup, Ndown, lam=LAM):
    N = L*L
    neighbors = build_neighbors(L)
    up_tuples, up_index = (st.build_ktuple_basis(N, Nup) if Nup>0 else ([()],{():0}))
    down_tuples, down_index = (st.build_ktuple_basis(N, Ndown) if Ndown>0 else ([()],{():0}))

    basis = []
    for u in up_tuples:
        uset = set(u)
        for d in down_tuples:
            if uset.isdisjoint(d):
                basis.append((u,d))
    index = {b:i for i,b in enumerate(basis)}
    D = len(basis)
    H = lil_matrix((D,D))

    for (u,d) in basis:
        col = index[(u,d)]
        occ = set(u) | set(d)
        for s in u:
            for nb in neighbors[s]:
                if nb in occ: continue
                new_u, sign = st.hop_ktuple(u, s, nb)
                H[index[(new_u,d)], col] += -lam*sign
        for s in d:
            for nb in neighbors[s]:
                if nb in occ: continue
                new_d, sign = st.hop_ktuple(d, s, nb)
                H[index[(u,new_d)], col] += -lam*sign
    return csr_matrix(H), D

def moments_via_traces(H, D):
    H2 = (H @ H)
    tr2 = H2.diagonal().sum()
    tr4 = (H2.multiply(H2)).sum()   # Tr(H^4) = sum_ab (H^2)_ab^2 for symmetric H
    mu2 = tr2/D
    mu4 = tr4/D
    return mu2, mu4

if __name__ == "__main__":
    print("module loaded")
