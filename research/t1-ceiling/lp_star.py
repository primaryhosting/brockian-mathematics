"""T1: full-species adversary LPs (A*, B*).

Adds to lp_primal3's on-line model the unconditional species:
  pair diagonal (m=1, depth y):        4 cosh^2(2 pi a y)          [count 2]
  pair-to-online cross at (y, Dx):     4 cosh(2 pi a y) cos(2 pi a Dx)   [count 0]
  pair-pair cross at (y, y', Dx):      4 cosh(2 pi a y)cosh(2 pi a y')cos(..Dx)
(cross masses >= 0; signs come from the cos factor -- both signs available by
choice of Dx, so these columns give the adversary signed cosh-weighted reads.)
All are exact contributions of real self-conjugate configurations to
S_emp(alpha) = |Z(alpha)|^2 / N >= 0.

B* adds S(alpha) >= 0 rows on (1, A].
"""
import numpy as np
from scipy.optimize import linprog
from lp_primal3 import make_cells, cell_cols, tail_cols, TAILB, MMAX

def solve_star(XF=160.0, na=1200, tol=2e-4, bochner_A=None, nb=None,
               depths=(0.1, 0.2, 0.3, 0.4, 0.5), dxs=None, label=""):
    if dxs is None:
        dxs = np.arange(0.0, 16.0, 0.125)
    lo, hi = make_cells(XF)
    ncell = len(lo)
    ntail = len(TAILB) + 1
    nd, nx = len(depths), len(dxs)
    ncross = nd * nx
    # vars: psi(MMAX) | pair-diag(nd) | cross(nd*nx) | eta(ncell) | tails(2*ntail)
    n = MMAX + nd + ncross + ncell + 2 * ntail
    iP = MMAX; iC = iP + nd; iE = iC + ncross; iT = iE + ncell

    ab = np.linspace(0.0, 1.0, na)
    rows_a = list(ab)
    if bochner_A is not None:
        if nb is None: nb = int(2 * (bochner_A - 1) * XF)
        rows_a += list(np.linspace(1.0 + 1e-3, bochner_A, nb))

    def srow(a):
        row = np.zeros(n)
        row[:MMAX] = np.arange(1, MMAX + 1) ** 2
        ch = np.cosh(2 * np.pi * a * np.asarray(depths))
        row[iP:iC] = 4 * ch ** 2
        cross = 4 * np.outer(ch, np.cos(2 * np.pi * a * dxs)).ravel()
        row[iC:iE] = cross
        row[iE:iT] = cell_cols(a, lo, hi)
        tc = tail_cols(a, XF)
        row[iT:iT + ntail] = tc
        row[iT + ntail:] = -tc
        return row

    nband = len(ab)
    A_ub, b_ub = [], []
    for i, a in enumerate(rows_a):
        r = srow(a)
        if i < nband:
            A_ub.append(r);  b_ub.append(a + tol)
            A_ub.append(-r); b_ub.append(-(a - tol))
        else:
            A_ub.append(-r); b_ub.append(tol)
    row = np.zeros(n)
    row[iT:iT + ntail - 1] = 1.0; row[iT + ntail:-1] = 1.0
    row[iT + ntail - 1] = 1 / np.pi ** 2; row[-1] = 1 / np.pi ** 2
    A_ub.append(row); b_ub.append(XF ** 2 * 0.9)

    A_eq = np.zeros((1, n))
    A_eq[0, :MMAX] = np.arange(1, MMAX + 1)
    A_eq[0, iP:iC] = 2.0
    b_eq = [1.0]
    bounds = ([(0, None)] * (MMAX + nd + ncross) + [(-1.0, None)] * ncell
              + [(0, None)] * (2 * ntail))
    c = np.zeros(n); c[0] = 1.0
    res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                  A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
    if res.success:
        psi = res.x[:MMAX]; pd = res.x[iP:iC]
        cr = res.x[iC:iE].reshape(nd, nx)
        print(f"[{label}] min psi_1 = {res.fun:.6f}  psi={np.round(psi, 5)}\n"
              f"    pair-diag masses {tuple(depths)} = {np.round(pd, 6)}\n"
              f"    cross mass by depth = {np.round(cr.sum(axis=1), 6)}",
              flush=True)
    else:
        print(f"[{label}] FAILED: {res.message}", flush=True)
    return res

if __name__ == "__main__":
    import sys
    which = sys.argv[1] if len(sys.argv) > 1 else "Astar"
    if which == "Astar":
        solve_star(XF=160., na=1200, tol=2e-4, label="A* XF=160")
        solve_star(XF=240., na=1800, tol=2e-4, label="A* XF=240")
    elif which == "Bstar":
        solve_star(XF=160., na=1200, tol=2e-4, bochner_A=3.0, label="B* XF=160 A=3")
    elif which == "B":
        # on-line Bochner (no pair species): the Rem 1.1 candidate
        solve_star(XF=160., na=1200, tol=2e-4, bochner_A=3.0, depths=(),
                   dxs=np.array([]), label="B XF=160 A=3")
        solve_star(XF=240., na=1800, tol=2e-4, bochner_A=3.0, depths=(),
                   dxs=np.array([]), label="B XF=240 A=3")
