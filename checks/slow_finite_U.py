"""Finite-U exact-diagonalization numbers quoted in the paper, recomputed with the paper's code.

    python checks/slow_finite_U.py evidence/YYYY-MM-DD-finite-U

* sec:benchmark#closure: the two-electron U-band at L = 7, U = 10, 15, 20: band centre against
  eps_d, band edge against eps_d + 4 t_d (derived sign) and eps_d + 4 t_d cos(pi/7) (opposite).
* sec:fewbody#centres, sec:n4test#threebands: sector means against N_d eps_d for n = 3 (2,1)
  at L = 5 and n = 4 (2,2), (3,1) at L = 4, U = 10 and 40, and against the bare U, 2U.
* sec:futurework#doublonflux-numeric: RMS residual of the doubled- and undoubled-phase doublon
  models against the exact flux-threaded U-band, L = 6 (all 36 quantized fluxes), U = 10, 20, 40, 80.
"""
import contextlib
import io
import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import dos_fig1  # noqa: E402
import four_electron as fe  # noqa: E402
import four_electron_31 as f31  # noqa: E402
import three_electron as te  # noqa: E402
import doublon_flux_validation as dv  # noqa: E402
from evidence_record import write_record  # noqa: E402


def eps_d(U):
    return U + 8 / U


def pct(a, b):
    return round(abs(a - b) / abs(b) * 100, 4)


def closure():
    A = dos_fig1.adjacency_matrix()
    out = {}
    for U in (10.0, 15.0, 20.0):
        band = np.sort(np.linalg.eigvalsh(dos_fig1.build_hamiltonian(A, U)))[-49:]
        td, ed = 2 / U, eps_d(U)
        out[f"U={U:g}"] = {
            "centre_dev_pct": pct(band.mean(), ed),
            "edge_dev_pct_derived_sign": pct(band.max(), ed + 4 * td),
            "edge_dev_pct_opposite_sign": pct(band.max(), ed + 4 * td * np.cos(np.pi / 7))}
    return out


def sector_means(H, Nd, U):
    w, v = np.linalg.eigh(H.toarray())
    nd = Nd(v)
    res = {}
    for k in (1, 2):
        m = np.abs(nd - k) < 0.5
        if m.any():
            E = w[m].mean()
            res[f"Nd={k}"] = {"count": int(m.sum()), "mean": round(float(E), 6),
                              "dev_pct_vs_Nd_eps_d": pct(E, k * eps_d(U)),
                              "dev_pct_vs_Nd_U": pct(E, k * U)}
    return res


def sectors():
    out = {}
    for U in (10.0, 40.0):
        H, ind, *_ = te.build_three_electron_H(5, U)
        out[f"n=3 (2,1) L=5 U={U:g}"] = sector_means(H, lambda v: te.n_d_expectation(v, ind), U)
        H, ind, *_ = fe.build_four_electron_H(4, U)
        out[f"n=4 (2,2) L=4 U={U:g}"] = sector_means(H, lambda v: fe.n_d_expectation(v, ind), U)
        H, ind, *_ = f31.build_H_31(4, U)
        out[f"n=4 (3,1) L=4 U={U:g}"] = sector_means(H, lambda v: f31.n_d_expectation(v, ind), U)
    return out


def flux():
    out = {}
    for U in (10.0, 20.0, 40.0, 80.0):
        with contextlib.redirect_stdout(io.StringIO()):
            *_, rms_d, rms_u, _ = dv.flux_sweep(L=6, U=U)
        ratio = rms_d.mean() / rms_u.mean()
        out[f"U={U:g}"] = {"rms_doubled_mean": float(rms_d.mean()),
                           "rms_undoubled_mean": float(rms_u.mean()),
                           "ratio": round(float(ratio), 4), "factor": round(float(1 / ratio), 2)}
    return out


def main(outdir):
    t0 = time.time()
    record = {"claims": ["sec:benchmark#closure", "sec:fewbody#centres", "sec:n4test#threebands",
                         "sec:futurework#doublonflux-numeric"],
              "closure_L7": closure(), "sector_centres": sectors(), "doublon_flux_L6": flux()}
    import json
    print(json.dumps(write_record(outdir, record, t0), indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
