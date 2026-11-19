"""eq:Aclosed#numeric and app:mu4walks#hcb-lemma: the closed forms against exact traces on every small graph.

    python checks/slow_mu4_intercept.py evidence/YYYY-MM-DD-mu4-intercept

1. Every simple graph with N <= 6 vertices (one per isomorphism class: 1, 2, 4, 11, 34, 156 classes),
   in every particle-number sector: mu4 of hard-core bosons against the lemma
   (2m + 4W + 8C4) p11 + (24D + 16C4) p22; and, for projected spin-1/2 fermions, in every spin
   composition, mu4 against A(N, n) + alpha(N, n) P_same (eq:Aclosed, eq:alphaN) and mu2 against the
   second-moment theorem.
2. 25 random graphs G(N, p) for each N = 7, 8, 9, 10 and p = 0.2, 0.35, 0.5, 0.7 (seed fixed), in every
   sector of dimension <= 6000.
Exact rationals throughout (lambda = 1). Fermionic traces use checks/hinf_local.py (sorted-tuple signs);
bosonic traces use mu4_closed_form.hcb_mu4_exact (token-graph enumeration).
Writes result.json, environment.json, command.txt and SHA256SUMS to the record directory.
"""
import random
import sys
import time
from fractions import Fraction
from itertools import combinations, permutations
from math import comb
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from evidence_record import write_record  # noqa: E402
from hinf_local import basis, h2_diag, h4_diag  # noqa: E402
import mu4_closed_form as m4c  # noqa: E402


def canonical_graphs(N):
    """One edge list per isomorphism class (minimum edge bitmask over relabellings)."""
    pairs = list(combinations(range(N), 2))
    pidx = {pr: k for k, pr in enumerate(pairs)}
    allm = np.arange(1 << len(pairs), dtype=np.int64)
    bits = [(allm >> k) & 1 for k in range(len(pairs))]
    canon = allm.copy()
    for perm in permutations(range(N)):
        new = np.zeros_like(allm)
        for k, (i, j) in enumerate(pairs):
            new |= bits[k] << pidx[tuple(sorted((perm[i], perm[j])))]
        np.minimum(canon, new, out=canon)
    return [[pairs[k] for k in range(len(pairs)) if (int(c) >> k) & 1] for c in np.unique(canon)]


def nbrs_of(N, edges):
    nb = [set() for _ in range(N)]
    for u, w in edges:
        nb[u].add(w)
        nb[w].add(u)
    return [sorted(s) for s in nb]


def check_graph(nb, max_dim):
    """(comparisons, failures) for one graph, every sector."""
    N = len(nb)
    cmp, fails = 0, []
    for n in range(N + 1):
        if comb(N, n) <= max_dim:
            cmp += 1
            if m4c.hcb_mu4_exact(nb, n) != m4c.mu4_hcb(nb, n):
                fails.append(("HCB", n))
        for ndn in range(n // 2 + 1):
            nup = n - ndn
            if comb(N, nup) * comb(N - nup, ndn) > max_dim:
                continue
            B = list(basis(N, nup, ndn))
            mu2 = Fraction(sum(h2_diag(x, nb) for x in B), len(B))
            mu4 = Fraction(sum(h4_diag(x, nb) for x in B), len(B))
            cmp += 2
            if mu2 != m4c.mu2(nb, n):
                fails.append(("mu2", nup, ndn))
            if mu4 != m4c.mu4_fermion(nb, nup, ndn):
                fails.append(("mu4", nup, ndn))
    return cmp, fails


def main(outdir):
    t0 = time.time()
    record = {"claims": ["eq:Aclosed#numeric", "app:mu4walks#hcb-lemma"], "exhaustive": {}, "random": {},
              "failures": []}
    for N in range(1, 7):
        graphs = canonical_graphs(N)
        cmp = 0
        for E in graphs:
            c, fl = check_graph(nbrs_of(N, E), max_dim=10 ** 6)
            cmp += c
            record["failures"] += [{"N": N, "edges": E, "sector": f} for f in fl]
        record["exhaustive"][N] = {"isomorphism_classes": len(graphs), "comparisons": cmp}
        print(f"N={N}: {len(graphs)} classes, {cmp} exact comparisons", flush=True)
    rng = random.Random(20261117)
    for N in range(7, 11):
        cmp = 0
        for prob in (0.2, 0.35, 0.5, 0.7):
            for _ in range(25):
                E = [e for e in combinations(range(N), 2) if rng.random() < prob]
                c, fl = check_graph(nbrs_of(N, E), max_dim=6000)
                cmp += c
                record["failures"] += [{"N": N, "edges": E, "sector": f} for f in fl]
        record["random"][N] = {"graphs": 100, "comparisons": cmp}
        print(f"N={N}: 100 random graphs, {cmp} exact comparisons", flush=True)
    record["total_comparisons"] = (sum(v["comparisons"] for v in record["exhaustive"].values())
                                   + sum(v["comparisons"] for v in record["random"].values()))
    record["all_exact"] = not record["failures"]
    write_record(outdir, record, t0)
    print(f"{record['total_comparisons']} exact comparisons, {len(record['failures'])} failures")
    return 0 if record["all_exact"] else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
