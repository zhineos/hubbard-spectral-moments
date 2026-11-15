"""Graph-generic U = infinity projected hopping H_inf = P0 H_t P0, applied to sparse states.

A configuration is (up_sites, down_sites), two sorted tuples with no common site. H_inf moves
one particle to an empty neighbouring site with amplitude -lam * sign, the sign given by the
sorted-tuple rule of sector_theory.hop_ktuple (the convention of uinf_traces_sparse.py).
States are dicts {configuration: amplitude}; nothing is ever built as a full matrix, so local
quantities such as (H^4)_aa = ||H^2 e_a||^2 cost only the neighbourhood of a.
"""
from collections import defaultdict
from itertools import combinations, product

import sector_theory as st


def torus_neighbors(shape):
    """Neighbour lists of the periodic hypercubic lattice with the given side lengths."""
    sites = list(product(*[range(L) for L in shape]))
    index = {s: i for i, s in enumerate(sites)}
    nbrs = []
    for s in sites:
        out = []
        for ax, L in enumerate(shape):
            for step in (1, -1):
                t = list(s)
                t[ax] = (t[ax] + step) % L
                out.append(index[tuple(t)])
        nbrs.append(sorted(set(out) - {index[s]}))
    return nbrs, index


def kagome_neighbors(L):
    """Neighbour lists of the periodic kagome lattice with L x L unit cells (3 sites each,
    coordination 4): up triangles (A, B, C) in each cell, down triangles B(R), A(R+a1),
    C(R+a1-a2)."""
    def idx(x, y, s):
        return ((x % L) * L + (y % L)) * 3 + s
    nb = [set() for _ in range(3 * L * L)]
    for x in range(L):
        for y in range(L):
            tri = [(idx(x, y, 0), idx(x, y, 1), idx(x, y, 2)),
                   (idx(x, y, 1), idx(x + 1, y, 0), idx(x + 1, y - 1, 2))]
            for a, b, c in tri:
                for u, v in ((a, b), (a, c), (b, c)):
                    nb[u].add(v)
                    nb[v].add(u)
    return [sorted(s) for s in nb]


def four_cycles(nbrs):
    """Number of 4-cycles (as subgraphs) of a simple graph."""
    from itertools import permutations
    E = {(a, b) for a in range(len(nbrs)) for b in nbrs[a]}
    return sum(1 for a, b, c, d in permutations(range(len(nbrs)), 4)
               if (a, b) in E and (b, c) in E and (c, d) in E and (d, a) in E) // 8


def small_graphs():
    """Test graphs for the graph-general alpha(N, n): K6, the Petersen graph, the 3 x 3
    triangular torus and a fixed random graph on 8 vertices."""
    import random
    out = {"K6": [[j for j in range(6) if j != i] for i in range(6)]}
    pet = {i: set() for i in range(10)}
    for i in range(5):
        for a, b in ((i, (i + 1) % 5), (i, i + 5), (i + 5, (i + 2) % 5 + 5)):
            pet[a].add(b)
            pet[b].add(a)
    out["Petersen"] = [sorted(pet[i]) for i in range(10)]
    tri = {i: set() for i in range(9)}
    for x in range(3):
        for y in range(3):
            for dx, dy in ((1, 0), (0, 1), (1, 1)):
                i, j = x * 3 + y, ((x + dx) % 3) * 3 + (y + dy) % 3
                tri[i].add(j)
                tri[j].add(i)
    out["triangular 3x3"] = [sorted(tri[i]) for i in range(9)]
    rng = random.Random(7)
    g = {i: set() for i in range(8)}
    for a, b in combinations(range(8), 2):
        if rng.random() < 0.45:
            g[a].add(b)
            g[b].add(a)
    out["random G(8,0.45), seed 7"] = [sorted(g[i]) for i in range(8)]
    return out


def apply_H(state, nbrs, lam=1):
    out = defaultdict(int)
    for (u, d), amp in state.items():
        occ = set(u) | set(d)
        for s in u:
            for nb in nbrs[s]:
                if nb in occ:
                    continue
                new_u, sign = st.hop_ktuple(u, s, nb)
                out[(new_u, d)] += -lam * sign * amp
        for s in d:
            for nb in nbrs[s]:
                if nb in occ:
                    continue
                new_d, sign = st.hop_ktuple(d, s, nb)
                out[(u, new_d)] += -lam * sign * amp
    return {k: v for k, v in out.items() if v != 0}


def h4_diag(config, nbrs):
    """(H^4)_aa = ||H^2 e_a||^2 (H real symmetric)."""
    v = apply_H(apply_H({config: 1}, nbrs), nbrs)
    return sum(a * a for a in v.values())


def h2_diag(config, nbrs):
    v = apply_H({config: 1}, nbrs)
    return sum(a * a for a in v.values())


def basis(N, nup, ndn):
    for u in combinations(range(N), nup):
        su = set(u)
        for d in combinations(range(N), ndn):
            if su.isdisjoint(d):
                yield (u, d)


def cfg(up, dn):
    return (tuple(sorted(up)), tuple(sorted(dn)))
