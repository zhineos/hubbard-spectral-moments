"""Theoretical moments for sums of independent cosine dispersions, and a
general k-fermion antisymmetrized hopping module (generalizes
three_electron.hop_pair to any number of identical fermions)."""
import numpy as np
from itertools import combinations

def theory_moments(amplitudes):
    """variance (mu2) and 4th central moment (mu4) of E=-2*sum(c_i*cos k_i),
    k_i independent uniform. Mean is 0 (add center separately)."""
    c = np.asarray(amplitudes, dtype=float)
    var = np.sum(2*c**2)                      # sum of per-term variances
    kappa4 = np.sum(-6*c**4)                   # 4th cumulant additive
    mu4 = kappa4 + 3*var**2
    return var, mu4

def empirical_moments(E):
    m = E.mean()
    c = E - m
    return m, np.mean(c**2), np.mean(c**4)

def wasserstein_to_samples(E, ref_samples):
    from scipy.stats import wasserstein_distance
    return wasserstein_distance(E, ref_samples)


# ---- general k-fermion antisymmetrized basis + hopping ----

def build_ktuple_basis(N, k):
    tuples = list(combinations(range(N), k))
    index = {t: i for i, t in enumerate(tuples)}
    return tuples, index

def hop_ktuple(t, s_from, s_to):
    """Move the fermion at site s_from (must be in t) to s_to (must not be
    in t). Returns (new_tuple_sorted, sign) via the standard sorted-tuple
    fermion sign rule (general for any k)."""
    if s_to in t:
        return None
    lst = list(t)
    m = lst.index(s_from)          # 0-indexed rank of the hopping fermion
    rest = lst[:m] + lst[m+1:]
    sign1 = (-1)**m                # (-1)^(m-1) with 0-indexed m -> (-1)^m... see derivation
    p = sum(1 for x in rest if x < s_to)
    sign2 = (-1)**p
    new_rest = rest[:p] + [s_to] + rest[p:]
    return tuple(new_rest), sign1*sign2

def build_H_ktuple(L, neighbors, tuples, index, lam):
    from scipy.sparse import lil_matrix, csr_matrix
    n = len(tuples)
    H = lil_matrix((n, n))
    for t in tuples:
        col = index[t]
        for s in t:
            for nb in neighbors[s]:
                res = hop_ktuple(t, s, nb)
                if res is None:
                    continue
                new_t, sign = res
                row = index[new_t]
                H[row, col] += -lam*sign
    return csr_matrix(H)
