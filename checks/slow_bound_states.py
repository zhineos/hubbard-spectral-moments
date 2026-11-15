"""sec:n3test#unbound: momentum-resolved search for doublon-electron bound states, n = 3.

    python checks/slow_bound_states.py evidence/YYYY-MM-DD-n3-bound-states

Two up electrons and one down electron on the L x L torus, exact Hubbard Hamiltonian
(three_electron.build_three_electron_H, all sectors). Total momentum K is conserved; every
translation orbit contains exactly one configuration with the down electron on site 0, so
each K block has dimension C(N, 2). In each block the U-band (N_d ~ 1, N - 1 states) is
compared with the doublon + electron continuum at that K,
    E(K, q) = eps_d + 2 t_d [cos(K_x - q_x) + cos(K_y - q_y)] - 2 lam [cos q_x + cos q_y],
and each state's relative-coordinate localization is measured by P_adj, the probability
(given N_d = 1) that the electron sits next to the doublon. A bound state lies outside the
continuum and keeps a finite P_adj as L grows; scattering states have P_adj ~ 4/(N - 1).
"""
import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import three_electron as te  # noqa: E402
from evidence_record import write_record  # noqa: E402

LAM = 1.0


def k_blocks(L, U, only=None):
    """Yield (K, H_K, doublon mask, adjacent mask) for every K = 2 pi (mx, my)/L, or only
    for the (mx, my) listed in `only`."""
    N = L * L
    H, ind, pairs, index, _ = te.build_three_electron_H(L, U, LAM)
    H = H.tocsc()
    reps = [(i, j) for (i, j) in pairs]               # down electron on site 0
    rep_index = {p: r for r, p in enumerate(reps)}
    xy = [divmod(s, L) for s in range(N)]

    def translate(s, bx, by):
        x, y = xy[s]
        return ((x + bx) % L) * L + (y + by) % L

    # column of each representative: matrix elements to arbitrary configurations c'',
    # each written as c'' = sign * T_b c' with c' a representative and b = down position
    cols, rows, vals, phase_b = [], [], [], []
    for r, (i, j) in enumerate(reps):
        col = index[(i, j)] * N + 0
        start, end = H.indptr[col], H.indptr[col + 1]
        for row, h in zip(H.indices[start:end], H.data[start:end]):
            p_idx, k = divmod(row, N)
            a, c = pairs[p_idx]
            bx, by = xy[k]
            a2, c2 = translate(a, -bx, -by), translate(c, -bx, -by)
            sign = 1 if a2 < c2 else -1
            rep2 = rep_index[(min(a2, c2), max(a2, c2))]
            cols.append(r); rows.append(rep2); vals.append(h * sign); phase_b.append((bx, by))
    cols, rows, vals = np.array(cols), np.array(rows), np.array(vals)
    bvec = np.array(phase_b, dtype=float)
    doublon = np.array([0 in p for p in reps])                       # N_d = 1 representatives
    neighbors0 = set(te.build_neighbors(L)[0])
    adjacent = np.array([0 in p and (set(p) - {0}) <= neighbors0 for p in reps])
    for mx in range(L):
        for my in range(L):
            if only is not None and (mx, my) not in only:
                continue
            K = 2 * np.pi * np.array([mx, my]) / L
            HK = np.zeros((len(reps), len(reps)), dtype=complex)
            np.add.at(HK, (rows, cols), vals * np.exp(-1j * bvec @ K))
            yield K, HK, doublon, adjacent


EDGE_TOL = 1e-9   # eigenvalues within this of a continuum edge count as on it (L = 6 has exact
                  # edge states E = U +- 4 lambda that floating point puts ~1e-14 outside)


def continuum(K, U, n=400):
    """Edges of the doublon + electron continuum at total momentum K (infinite lattice)."""
    td, ed = 2 * LAM ** 2 / U, U + 8 * LAM ** 2 / U
    q = np.linspace(-np.pi, np.pi, n, endpoint=False)
    qx, qy = np.meshgrid(q, q)
    E = ed + 2 * td * (np.cos(K[0] - qx) + np.cos(K[1] - qy)) - 2 * LAM * (np.cos(qx) + np.cos(qy))
    return E.min(), E.max()


def run(L, U):
    N = L * L
    worst_out, max_padj, outside = -np.inf, 0.0, []
    for K, HK, doublon, adjacent in k_blocks(L, U):
        assert np.allclose(HK, HK.conj().T, atol=1e-12)
        w, v = np.linalg.eigh(HK)
        P = np.abs(v) ** 2
        nd = doublon @ P
        band = np.where(nd > 0.5)[0]
        assert len(band) == N - 1, (L, K, len(band))
        padj = (adjacent @ P[:, band]) / (doublon @ P[:, band])
        lo, hi = continuum(K, U)
        for e, pa in zip(w[band], padj):
            out = max(lo - e, e - hi)                   # > 0: outside the continuum
            worst_out = max(worst_out, out)
            max_padj = max(max_padj, pa)
            if out > EDGE_TOL:                           # beyond rounding at the edge
                outside.append({"K/2pi*L": [round(K[0] * L / (2 * np.pi)), round(K[1] * L / (2 * np.pi))],
                                "E": round(float(e), 5), "distance_outside": round(float(out), 5),
                                "P_adj": round(float(pa), 4)})
    return {"L": L, "U": U, "uniform_P_adj": round(4 / (N - 1), 4),
            "max_P_adj": round(float(max_padj), 4),
            "largest_distance_outside_continuum": round(float(worst_out), 5),
            "states_outside": sorted(outside, key=lambda d: -d["distance_outside"])[:6],
            "n_states_outside": len(outside)}


def k0_weights(L, U):
    """K = 0: energies of the U-band and the weight of each eigenstate on the four
    configurations with the electron next to the doublon."""
    (K, HK, doublon, adjacent), = k_blocks(L, U, only=[(0, 0)])
    assert np.abs(HK.imag).max() < 1e-12
    w, v = np.linalg.eigh(HK.real)
    P = v ** 2
    band = np.where(doublon @ P > 0.5)[0]
    W = adjacent @ P[:, band]
    return w[band] - (U + 8 * LAM ** 2 / U), W


def main(outdir):
    import doublon_electron_first_order as fo
    t0 = time.time()
    U = 30.0
    record = {"claim": "sec:n3test#unbound", "U": U}
    # 1. exact, every K sector, U = 30
    record["exact_all_K"] = []
    for L in (4, 5, 6, 7, 8, 9):
        r = run(L, U)
        record["exact_all_K"].append(r)
        print(f"exact L={L}: outside {r['n_states_outside']}, largest distance outside "
              f"{r['largest_distance_outside_continuum']:+.5f}, max P_adj {r['max_P_adj']} "
              f"(uniform {r['uniform_P_adj']})", flush=True)
    # 2. exact, K = 0: weight of each U-band state on the four adjacent configurations
    record["exact_K0_weights"] = []
    for L in (6, 7, 8, 9, 10, 11, 12):
        E, W = k0_weights(L, U)
        o = np.argsort(-W)[:3]
        record["exact_K0_weights"].append({"L": L, "sum_W": round(float(W.sum()), 4),
            "max_W": round(float(W.max()), 4),
            "participation": round(float(W.sum() ** 2 / (W ** 2).sum()), 2),
            "top": [[round(float(W[i]), 4), round(float(E[i]), 4)] for i in o]})
        print(f"exact K=0 L={L}: max W {W.max():.4f}", flush=True)
    # 3. first-order model: validation, all-K scan, resonance weights to L = 64
    val = []
    for (mx, my) in [(0, 0), (1, 0), (1, 2), (3, 3)]:
        (K, HK, dbl, adj), = k_blocks(6, 2000.0, only=[(mx, my)])
        w = np.linalg.eigvalsh(HK)
        band = np.sort(w[w > 1000.0]) - 2000.0
        e1 = np.sort(np.linalg.eigvalsh(fo.block(6, K)[0]))
        val.append(round(float(np.abs(band - e1).max()), 5))
    record["first_order_validation_L6_U2000_max_dev"] = val
    scan = []
    for L in (24, 32):
        worst, n_out = -np.inf, 0
        for mx in range(L):
            for my in range(L):
                w = np.linalg.eigvalsh(fo.block(L, 2 * np.pi * np.array([mx, my]) / L)[0])
                worst = max(worst, -4 - w.min(), w.max() - 4)
                n_out += int(((w < -4 - 1e-9) | (w > 4 + 1e-9)).sum())
        scan.append({"L": L, "states_outside_band": n_out, "largest_excursion": float(worst)})
        print(f"first order L={L}: outside {n_out}", flush=True)
    record["first_order_all_K"] = scan
    res = []
    for L in (8, 12, 16, 24, 32, 48, 64):
        H, sites = fo.block(L, (0.0, 0.0))
        w, v = np.linalg.eigh(H.real)
        adj = [n for n, (x, y) in enumerate(sites) if min(x, L - x) + min(y, L - y) == 1]
        W = (v[adj, :] ** 2).sum(0)
        o = np.argsort(-W)[:3]
        res.append({"L": L, "max_W": round(float(W.max()), 4),
                    "top": [[round(float(W[i]), 4), round(float(w[i]), 4)] for i in o]})
    record["first_order_K0_resonance"] = res
    write_record(outdir, record, t0)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
