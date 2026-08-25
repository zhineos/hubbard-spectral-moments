#!/usr/bin/env python3
"""
Diagnostic requested before freezing Fig. 3: is the small displacement
of the exact sector mean energy from the isolated-cluster prediction
N_d*eps_d an O(lambda^2/U) many-particle correction (U*Delta -> const)
or a genuinely higher-order O(lambda^3/U^2) effect (U*Delta -> 0,
U^2*Delta -> const)?

Full dense diagonalization (exact, not extremal/sampled), same
construction as verify_sectors_provenance.py, extended to more U
values and to both U*Delta and U^2*Delta scaling.
"""
import numpy as np
import three_electron as te
import four_electron as fe

LAM = 1.0
U_VALUES = [10.0, 15.0, 20.0, 30.0, 40.0, 60.0]


def eps_d(U, lam=LAM):
    return U + 8 * lam**2 / U


def analyze(label, build_fn, Nd_targets):
    print("=" * 78)
    print(label)
    print("=" * 78)
    rows = {k: [] for k in Nd_targets}
    for U in U_VALUES:
        H, indicator, *_ = build_fn(U)
        w, v = np.linalg.eigh(H.toarray())
        Nd = indicator @ (np.abs(v) ** 2)
        print(f"U={U:g}:")
        for k in Nd_targets:
            mask = np.abs(Nd - k) < 0.5
            Ek = w[mask]
            Ebar = Ek.mean()
            pred = k * eps_d(U)
            Delta = Ebar - pred
            UD = U * Delta
            U2D = U**2 * Delta
            rows[k].append((U, Delta, UD, U2D))
            print(f"  Nd~{k}: n={mask.sum():6d}  <E>={Ebar:14.8f}  "
                  f"pred={pred:14.8f}  Delta={Delta:+.8f}  "
                  f"U*Delta={UD:+.6f}  U^2*Delta={U2D:+.6f}")
        print()
    print(f"--- {label}: scaling summary ---")
    for k in Nd_targets:
        if k == 0:
            continue
        Us = np.array([r[0] for r in rows[k]])
        UDs = np.array([r[2] for r in rows[k]])
        U2Ds = np.array([r[3] for r in rows[k]])
        print(f"Nd={k}: U*Delta across U={list(Us)}:")
        print(f"       {list(np.round(UDs, 5))}")
        print(f"Nd={k}: U^2*Delta across U={list(Us)}:")
        print(f"       {list(np.round(U2Ds, 4))}")
        # crude convergence check: is U*Delta flattening (O(1/U) real effect)
        # or is U*Delta itself ~1/U (i.e. -> 0, so U^2*Delta flattens instead)?
        UD_drift = abs(UDs[-1] - UDs[-2]) / (abs(UDs[-2]) + 1e-12)
        U2D_drift = abs(U2Ds[-1] - U2Ds[-2]) / (abs(U2Ds[-2]) + 1e-12)
        verdict = "U*Delta -> const (O(1/U) many-body correction)" if UD_drift < U2D_drift \
            else "U^2*Delta -> const (genuinely higher order, O(1/U^2))"
        print(f"Nd={k}: relative drift of last two points: U*Delta {UD_drift:.4f}, "
              f"U^2*Delta {U2D_drift:.4f}  =>  {verdict}")
        print()


def build3(U):
    H, indicator, pairs, index, N = te.build_three_electron_H(5, U)
    return H, indicator, pairs, index, N


def build4(U):
    H, indicator, pairs, index, N = fe.build_four_electron_H(4, U)
    return H, indicator, pairs, index, N


if __name__ == "__main__":
    analyze("n=3 (2up+1down), L=5, N=25", build3, Nd_targets=[0, 1])
    analyze("n=4 (2up+2down), L=4, N=16", build4, Nd_targets=[0, 1, 2])
