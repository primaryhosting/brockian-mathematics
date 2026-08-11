"""W2: solve the EXACT-cone 2-level relaxation as a true SOCP (Clarabel),
at the referee's own discretization (XF=80, na=600, A=3, nb=320, tol=2e-4,
depths 0.1..0.5).  Corroborates witness_psi0.py: expected min psi_1 = 0
(up to solver tolerance), settling what the 12-round cutting-plane probe
(residual stuck at +0.038) could not.

Also runs the pairs-off restriction (p == 0, which forces S_P = 0, X = 0):
the model then collapses to the on-line Variant-A LP, whose value should sit
near the refereed V_A landscape (T1: 0.679 at XF=80 coarse grid) -- showing
the collapse to 0 is driven ENTIRELY by the pair channel + free correlation
cells, not by a bug.

Run with the venv python: ./venv/bin/python socp_exact.py
"""
import sys
import numpy as np
import cvxpy as cp

T1 = "/Users/acutis/Projects/brockian-mathematics/research/t1-ceiling"
sys.path.insert(0, T1)
from lp_primal3 import make_cells, cell_cols, tail_cols, TAILB, MMAX  # noqa: E402


def solve_exact_socp(XF=80.0, na=600, tol=2e-4, Aboch=3.0, nb=320,
                     depths=(0.1, 0.2, 0.3, 0.4, 0.5), use_pairs=True,
                     label=""):
    lo, hi = make_cells(XF)
    ncell = len(lo); ntail = len(TAILB) + 1
    nd = len(depths)
    ab = np.linspace(0.0, 1.0, na)
    ao = np.linspace(1.0 + 1e-3, Aboch, nb)
    aa = np.concatenate([ab, ao]); nA = len(aa)

    # dense structure matrices (same formulas as lp_cone / cone_socp)
    Ccells = np.zeros((nA, ncell))
    Tt = np.zeros((nA, ntail))
    Pk = np.zeros((nA, nd))
    for i, a in enumerate(aa):
        Ccells[i] = cell_cols(a, lo, hi)
        Tt[i] = tail_cols(a, XF)
        for k, y in enumerate(depths):
            Pk[i, k] = 4 * np.cosh(2 * np.pi * a * y) ** 2
    m2 = np.arange(1, MMAX + 1) ** 2

    psi = cp.Variable(MMAX, nonneg=True)
    p = cp.Variable(nd, nonneg=True)
    eta = cp.Variable(ncell)
    tails = cp.Variable(2 * ntail, nonneg=True)
    SO = cp.Variable(nA, nonneg=True)
    SP = cp.Variable(nA, nonneg=True)
    X = cp.Variable(nA)

    cons = [
        SO == m2 @ psi + Ccells @ eta + Tt @ (tails[:ntail] - tails[ntail:]),
        SP == Pk @ p,
        np.arange(1, MMAX + 1) @ psi + 2 * cp.sum(p) == 1.0,
        eta >= -1.0,
        # band equalities (tol as in the referee's model)
        SO[:na] + SP[:na] + X[:na] <= ab + tol,
        SO[:na] + SP[:na] + X[:na] >= ab - tol,
        # out-of-band Bochner
        SO[na:] + SP[na:] + X[na:] >= -tol,
        # tail budget
        (cp.sum(tails[:ntail - 1]) + cp.sum(tails[ntail:2 * ntail - 1])
         + (tails[ntail - 1] + tails[2 * ntail - 1]) / np.pi ** 2)
        <= XF ** 2 * 0.9,
    ]
    if use_pairs:
        # EXACT cone: X^2 <= 4 SO SP  <=>  || (X, SO - SP) ||_2 <= SO + SP
        cons.append(cp.SOC(SO + SP, cp.vstack([X, SO - SP]), axis=0))
    else:
        cons += [p == 0, X == 0]

    prob = cp.Problem(cp.Minimize(psi[0]), cons)
    prob.solve(solver=cp.CLARABEL, verbose=False)
    print(f"[{label}] status = {prob.status}   min psi_1 = {prob.value:.8f}")
    if prob.status in ("optimal", "optimal_inaccurate"):
        so, sp, xv = SO.value, SP.value, X.value
        resid = np.abs(xv) - 2 * np.sqrt(np.maximum(so, 0) * np.maximum(sp, 0))
        print(f"    psi = {np.round(psi.value, 6)}   p = {np.round(p.value, 6)}")
        print(f"    exact-CS residual at solver point: max = {resid.max():+.3e}"
              f"  (solver feasibility tolerance scale)")
    return prob.value


if __name__ == "__main__":
    v = solve_exact_socp(label="exact-cone SOCP, referee grid XF=80 na=600 A=3")
    print()
    vA = solve_exact_socp(use_pairs=False,
                          label="pairs OFF (p=0 -> X=0): on-line Variant-A")
    print(f"\nSummary: exact-cone min psi_1 = {v:.6f} (witness proves exactly 0); "
          f"pairs-off min psi_1 = {vA:.6f} (V_A landscape, grid-indexed "
          f"XF=80/na=600/A=3).")
