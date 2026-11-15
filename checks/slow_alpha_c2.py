"""eq:alphaN#numeric, sec:SW#beta-trend and sec:SW#c2-sign: the slow cases of the review rounds of 2026-11-13 and 2026-11-14.

    python checks/slow_alpha_c2.py evidence/YYYY-MM-DD-alpha-c2

1. The closed form alpha(N, n) = -8 (N-n)(8N-11n-2) / [(N-1)(N-2)(N-3)] against the exact slopes
   of mu_4(U = inf) in P_same, for every pair of adjacent compositions, at L = 6, n = 4 and 5
   (exact rationals at lambda = 1; the faster cases are in checks/run_checks.py).
2. The U^-2 coefficient c2 = Var(V) + 2 Tr(T0 H3)/D0 of mu_2c(U) for n = 5 at L = 5 and L = 6,
   (4,1) and (3,2): the sign of c2 (sec:SW#c2-sign: negative in every low-filling sector computed)
   and the relative spread |x - y| / mean(|x|, |y|) of c2/(N_up N_down) between the two
   compositions (the paper prints 0.13 % at L = 5). L = 6 takes a few minutes.
Writes result.json, environment.json, command.txt and SHA256SUMS to the record directory.
"""
import sys
import time
from fractions import Fraction
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from evidence_record import write_record  # noqa: E402
from sw_correction import sw_moments  # noqa: E402
from uinf_traces_sparse import build_Uinf_H_sparse  # noqa: E402


def exact(x):
    r = round(x)
    assert abs(x - r) < 1e-6, x
    return r


def mu4(L, a, b):
    H, D = build_Uinf_H_sparse(L, a, b, lam=1.0)
    H2 = H @ H
    return Fraction(exact(H2.multiply(H2).sum()), D)


def alpha_formula(N, n):
    return Fraction(-8 * (N - n) * (8 * N - 11 * n - 2), (N - 1) * (N - 2) * (N - 3))


def c2(L, a, b):
    m = sw_moments(L, a, b, lam=1.0, third_order=True)
    D0 = m["D0"]
    var_v = Fraction(exact(m["tr_Vsq"]), D0) - Fraction(exact(m["tr_V"]), D0) ** 2
    return var_v + 2 * Fraction(exact(m["tr_T0H3"]), D0)


def main(outdir):
    t0 = time.time()
    record = {"claims": ["eq:alphaN#numeric", "sec:SW#beta-trend", "sec:SW#c2-sign"], "alpha": [], "c2": {}}
    for L, n in [(6, 4), (6, 5)]:
        comps = [(n - k, k) for k in range(n // 2 + 1)]
        m = {c: mu4(L, *c) for c in comps}
        ps = {c: comb(c[0], 2) + comb(c[1], 2) for c in comps}
        slopes = [(m[c] - m[d]) / (ps[c] - ps[d]) for c, d in zip(comps, comps[1:])]
        f = alpha_formula(L * L, n)
        record["alpha"].append({"L": L, "n": n, "slopes": [str(s) for s in slopes], "formula": str(f),
                                "all_equal_formula": all(s == f for s in slopes)})
        print(record["alpha"][-1], flush=True)
    record["c2"] = []
    for L in (5, 6):
        c41, c32 = c2(L, 4, 1), c2(L, 3, 2)
        b41, b32 = c41 / 4, c32 / 6
        record["c2"].append({"L": L, "n": 5, "c2(4,1)": str(c41), "c2(3,2)": str(c32),
                             "c2_negative": bool(c41 < 0 and c32 < 0),
                             "c2/NuNd (4,1)": float(b41), "c2/NuNd (3,2)": float(b32),
                             "relative_spread_percent":
                                 round(float(abs(b32 - b41) / ((abs(b32) + abs(b41)) / 2)) * 100, 3)})
        print(record["c2"][-1], flush=True)
    write_record(outdir, record, t0)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
