"""tab:n6test: the over-determined n = 6 linearity test at L = 5, as exact rationals.

    python checks/slow_n6_linearity.py evidence/YYYY-MM-DD-n6-linearity

For each spin composition (6,0), (5,1), (4,2), (3,3) of n = 6 particles on the 5 x 5 torus,
computes mu_2 = Tr(H^2)/D and mu_4 = Tr(H^4)/D of H_inf exactly (lambda = 1), and checks that
the four (P_same, mu_4) points lie on one line exactly.

Tr(H^l) = sum_a (H^l)_aa, with (H^4)_aa = ||H^2 e_a||^2. The diagonal elements are invariant
under lattice translations, so sum_a f(a) = (N / N_up) * sum over the configurations with an
up particle on site 0 (each configuration has N_up up particles, and each translate puts one
of them on site 0). Writes result.json, environment.json, command.txt and SHA256SUMS to the
record directory.
"""
import hashlib
import json
import os
import platform
import resource
import subprocess
import sys
import time
from fractions import Fraction
from itertools import combinations
from math import comb
from multiprocessing import Pool
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from hinf_local import h2_diag, h4_diag, torus_neighbors  # noqa: E402

L = 5
N = L * L
NB, _ = torus_neighbors((L, L))
PAPER = {(6, 0): "1002.343874", (5, 1): "1010.604743", (4, 2): "1015.561265", (3, 3): "1017.213439"}


def chunk_sums(args):
    up_rest, nup, ndn = args
    t2 = t4 = 0
    for rest in up_rest:
        u = (0,) + rest
        others = [x for x in range(N) if x not in u]
        for d in combinations(others, ndn):
            t2 += h2_diag((u, d), NB)
            t4 += h4_diag((u, d), NB)
    return t2, t4


def moments(nup, ndn, pool):
    rests = list(combinations(range(1, N), nup - 1))
    chunks = [(rests[i::64], nup, ndn) for i in range(64)]
    t2 = t4 = 0
    for a, b in pool.imap_unordered(chunk_sums, chunks):
        t2 += a
        t4 += b
    D = comb(N, nup) * comb(N - nup, ndn)
    # undo the restriction to configurations with an up particle on site 0
    tr2, tr4 = Fraction(t2 * N, nup), Fraction(t4 * N, nup)
    assert tr2.denominator == 1 and tr4.denominator == 1
    return D, int(tr2), int(tr4)


def main(outdir):
    out = Path(outdir)
    out.mkdir(parents=True, exist_ok=False)
    t0 = time.time()
    results = {}
    with Pool() as pool:
        for comp in [(6, 0), (5, 1), (4, 2), (3, 3)]:
            D, tr2, tr4 = moments(*comp, pool)
            psame = comb(comp[0], 2) + comb(comp[1], 2)
            mu2, mu4 = Fraction(tr2, D), Fraction(tr4, D)
            results[comp] = (psame, mu2, mu4)
            print(f"{comp}: D={D} P_same={psame} mu2={mu2} mu4={mu4} = {float(mu4):.6f}"
                  f" (paper {PAPER[comp]})", flush=True)
    pts = [results[c] for c in [(6, 0), (5, 1), (4, 2), (3, 3)]]
    slopes = [(b[2] - a[2]) / (b[0] - a[0]) for a, b in zip(pts, pts[1:])]
    exact_line = len(set(slopes)) == 1
    alpha = slopes[0]
    A = pts[0][2] - alpha * pts[0][0]
    wall = time.time() - t0
    record = {
        "claim": "tab:n6test",
        "lattice": "5x5 torus", "n": 6, "lambda": 1,
        "compositions": {f"{c[0]},{c[1]}": {
            "D": comb(N, c[0]) * comb(N - c[0], c[1]), "P_same": results[c][0],
            "mu2": str(results[c][1]), "mu4": str(results[c][2]),
            "mu4_decimal": f"{float(results[c][2]):.6f}", "paper": PAPER[c],
            "matches_paper_to_6_decimals": f"{float(results[c][2]):.6f}" == PAPER[c]}
            for c in results},
        "slopes_between_consecutive_points": [str(x) for x in slopes],
        "exactly_linear_in_P_same": exact_line,
        "A": str(A), "alpha": str(alpha),
        "wall_time_s": round(wall, 1),
        "peak_rss_mb": round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2 ** 20, 1)
        if platform.system() == "Darwin" else
        round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2 ** 10, 1),
    }
    print(json.dumps(record, indent=2))
    commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True,
                            text=True).stdout.strip()
    dirty = subprocess.run(["git", "-C", str(ROOT), "status", "--porcelain"], capture_output=True,
                           text=True).stdout.strip() != ""
    env = {"date": time.strftime("%Y-%m-%d %H:%M:%S %Z"), "machine": platform.machine(),
           "os": platform.platform(), "cpus": os.cpu_count(), "python": platform.python_version(),
           "git_commit": commit, "working_tree_dirty": dirty}
    (out / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    (out / "environment.json").write_text(json.dumps(env, indent=2) + "\n")
    (out / "command.txt").write_text(" ".join([Path(sys.executable).name] + sys.argv) + "\n")
    sums = "".join(f"{hashlib.sha256((out / f).read_bytes()).hexdigest()}  {f}\n"
                   for f in ["command.txt", "environment.json", "result.json"])
    (out / "SHA256SUMS").write_text(sums)
    return 0 if exact_line and all(v["matches_paper_to_6_decimals"]
                                   for v in record["compositions"].values()) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
