"""Four electrons, 3 up-spin + 1 down-spin, on an LxL lattice.
Basis: antisymmetrized up-triple (k=3) x down single-particle index.
N_d in {0,1}: 1 if the down electron's site is among the up-triple."""
import numpy as np
from scipy.sparse import kron, identity, diags, csr_matrix
import sector_theory as st
from three_electron import LAM, build_neighbors, adjacency_matrix

def build_H_31(L, U, lam=LAM):
    N = L*L
    neighbors = build_neighbors(L)
    A = adjacency_matrix(L, neighbors, lam)
    tuples, index = st.build_ktuple_basis(N, 3)
    H_uuu = st.build_H_ktuple(L, neighbors, tuples, index, lam)
    n_t = len(tuples)
    I_t = identity(n_t, format="csr")
    I_N = identity(N, format="csr")
    H = kron(H_uuu, I_N) + kron(I_t, A)

    indicator = np.zeros(n_t*N)
    for t_idx, trip in enumerate(tuples):
        base = t_idx*N
        for s in trip:
            indicator[base+s] = 1.0
    H = H + U*diags(indicator)
    return csr_matrix(H), indicator, tuples, N

def n_d_expectation(eigenvectors, indicator):
    return indicator @ (np.abs(eigenvectors)**2)

if __name__ == "__main__":
    print("module loaded")
