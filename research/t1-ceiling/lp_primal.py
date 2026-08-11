"""T1: tolerant primal adversary LP (variants A/B/C) with refinement study.

min psi_1 over species (on-line mult m=1..5; off-line pairs at depths y) and
correlation density eta >= -1 on [0,X], subject to
  band:  |sum_m m^2 psi_m + sum_k 4cosh^2(2 pi a y_k) p_k
          + 2h sum_j eta_j cos(2 pi a x_j) - a| <= tol   for a in [0,1] grid
  count: sum_m m psi_m + 2 sum_k p_k = 1
  (B/C)  S(a) >= -tol for a in (1,A] grid.
"""
import numpy as np
from scipy.optimize import linprog

MMAX = 5

def solve(X=24.0, h=0.02, na=161, tol=1e-3, bochner_A=None, nb=480,
          depths=(), label=""):
    xg = np.arange(h / 2, X, h)
    ab = np.linspace(0.0, 1.0, na)
    npair, neta = len(depths), len(xg)
    n = MMAX + npair + neta
    iP, iE = MMAX, MMAX + npair

    def srow(a):
        row = np.zeros(n)
        row[:MMAX] = np.arange(1, MMAX + 1) ** 2
        for k, y in enumerate(depths):
            row[iP + k] = 4 * np.cosh(2 * np.pi * a * y) ** 2
        row[iE:] = 2 * h * np.cos(2 * np.pi * a * xg)
        return row

    A_ub, b_ub = [], []
    for a in ab:
        r = srow(a)
        A_ub.append(r); b_ub.append(a + tol)
        A_ub.append(-r); b_ub.append(-(a - tol))
    if bochner_A is not None:
        for a in np.linspace(1.0 + 1e-3, bochner_A, nb):
            A_ub.append(-srow(a)); b_ub.append(tol)

    A_eq = np.zeros((1, n))
    A_eq[0, :MMAX] = np.arange(1, MMAX + 1)
    A_eq[0, iP:iE] = 2.0
    b_eq = [1.0]
    bounds = [(0, None)] * (MMAX + npair) + [(-1.0, None)] * neta
    c = np.zeros(n); c[0] = 1.0

    res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                  A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
    if res.success:
        psi = res.x[:MMAX]; pr = res.x[iP:iE]
        msg = (f"[{label}] min psi_1 = {res.fun:.6f}  psi={np.round(psi,5)}")
        if npair:
            msg += f"  pairs={np.round(pr, 6)}"
        print(msg)
    else:
        print(f"[{label}] FAILED: {res.message}")
    return res

if __name__ == "__main__":
    print("--- Variant A (band only), tolerance study; expect -> 0.672501 ---")
    for tol in (2e-3, 1e-3, 5e-4):
        solve(tol=tol, label=f"A tol={tol}")

    print("\n--- Variant B (+ S>=0 on (1,4]); paper Rem 1.1 => 0.68185? ---")
    for tol in (2e-3, 1e-3, 5e-4):
        solve(tol=tol, bochner_A=4.0, label=f"B tol={tol}")

    print("\n--- Variant C (B + off-line pairs at depths) ---")
    for dep in [(0.1, 0.2), (0.1, 0.2, 0.3, 0.4), (0.1, 0.2, 0.3, 0.4, 0.5, 0.6)]:
        solve(tol=1e-3, bochner_A=4.0, depths=dep, label=f"C depths<= {dep[-1]}")
