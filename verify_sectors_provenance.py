#!/usr/bin/env python3
"""
Independent data-provenance check for Fig. 3, run BEFORE any plotting.
Full dense diagonalization (not the extremal/projected sampling used
for the figure) so that sector STATE COUNTS are exact, not sampled.

For each case, prints:
  D (total dimension), #states with Nd~0,1,2 (rounded to nearest
  integer, tolerance 0.5), <E> for each sector, the predicted eps_d /
  2*eps_d, and the deviation Delta.

Combinatorial predictions to check against (atomic/large-U limit):
  n=3 (2up+1down), L=5, N=25: D=7500
    Nd=1 count = N*(N-1) = 600 ; Nd=0 count = D-600 = 6900
  n=4 (2up+2down), L=4, N=16: D=14400
    Nd=2 count = C(N,2) = 120
    Nd=1 count = N*(N-1)*(N-2) = 3360
    Nd=0 count = D-120-3360 = 10920
"""
import numpy as np
import three_electron as te
import four_electron as fe

LAM = 1.0


def eps_d(U, lam=LAM):
    return U + 8 * lam**2 / U


def sector_report(w, Nd, D, label):
    print(f"  D={D}")
    for k in sorted(set(np.round(Nd).astype(int))):
        mask = np.abs(Nd - k) < 0.5
        n_k = mask.sum()
        Ek = w[mask]
        print(f"    Nd~{k}: count={n_k:6d}  <E>={Ek.mean():12.6f}  "
              f"std={Ek.std():8.4f}  range=[{Ek.min():.3f},{Ek.max():.3f}]")
    return


print("=" * 70)
print("n=3 (2up+1down), L=5, N=25  [predicted: Nd=0 -> 6900, Nd=1 -> 600]")
print("=" * 70)
for U in [10.0, 20.0, 40.0, 100.0]:
    H, indicator, pairs, index, N = te.build_three_electron_H(5, U)
    D = H.shape[0]
    w, v = np.linalg.eigh(H.toarray())
    Nd = te.n_d_expectation(v, indicator)
    print(f"U={U:g}:")
    sector_report(w, Nd, D, "n=3")
    mask1 = np.abs(Nd - 1) < 0.5
    E1 = w[mask1].mean()
    pred = eps_d(U)
    print(f"    predicted eps_d={pred:.6f}  Delta=<E>_Nd1-eps_d={E1-pred:+.6f}")
    print()

print("=" * 70)
print("n=4 (2up+2down), L=4, N=16  [predicted: Nd=0->10920, Nd=1->3360, Nd=2->120]")
print("=" * 70)
for U in [10.0, 20.0, 40.0, 100.0]:
    H, indicator, pairs, index, N = fe.build_four_electron_H(4, U)
    D = H.shape[0]
    w, v = np.linalg.eigh(H.toarray())
    Nd = fe.n_d_expectation(v, indicator)
    print(f"U={U:g}:")
    sector_report(w, Nd, D, "n=4")
    mask1 = np.abs(Nd - 1) < 0.5
    mask2 = np.abs(Nd - 2) < 0.5
    E1 = w[mask1].mean()
    E2 = w[mask2].mean()
    pred1 = eps_d(U)
    pred2 = 2 * eps_d(U)
    print(f"    predicted eps_d={pred1:.6f}    Delta1={E1-pred1:+.6f}")
    print(f"    predicted 2eps_d={pred2:.6f}   Delta2={E2-pred2:+.6f}")
    print()
