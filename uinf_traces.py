"""Exact P0 H_t P0 (U=infinity, no double occupancy of any kind) for
general (Nup, Ndown) on an LxL lattice. Small enough to just build and
diagonalize directly for modest N_up+N_down."""
import numpy as np
from itertools import combinations
import sector_theory as st
from three_electron import build_neighbors, LAM

def build_Uinf_H(L, Nup, Ndown, lam=LAM):
    N = L*L
    neighbors = build_neighbors(L)

    up_tuples, up_index = st.build_ktuple_basis(N, Nup) if Nup>0 else ([()],{():0})
    down_tuples, down_index = st.build_ktuple_basis(N, Ndown) if Ndown>0 else ([()],{():0})

    # only keep (up_set, down_set) pairs that are disjoint (U=inf constraint)
    basis = []
    for u in up_tuples:
        uset = set(u)
        for d in down_tuples:
            if uset.isdisjoint(d):
                basis.append((u,d))
    index = {b:i for i,b in enumerate(basis)}
    D = len(basis)
    H = np.zeros((D,D))

    def hop_tuple_general(t, s_from, s_to):
        if len(t)==0:
            return None
        return st.hop_ktuple(t, s_from, s_to)

    for (u,d) in basis:
        col = index[(u,d)]
        occ = set(u) | set(d)
        # up hops
        for s in u:
            for nb in neighbors[s]:
                if nb in occ:
                    continue
                res = st.hop_ktuple(u, s, nb)
                new_u, sign = res
                row = index[(new_u, d)]
                H[row, col] += -lam*sign
        # down hops
        for s in d:
            for nb in neighbors[s]:
                if nb in occ:
                    continue
                res = st.hop_ktuple(d, s, nb)
                new_d, sign = res
                row = index[(u, new_d)]
                H[row, col] += -lam*sign
    return H, basis

if __name__ == "__main__":
    print("module loaded")
