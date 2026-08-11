"""W3: exact-cone (Clarabel SOCP) values for the ladder levels.

The LP in ladder.py outer-approximates the cone by t-grid rows, so LP value
<= SOCP value; LP DUALS remain valid lower bounds for the exact-cone class
(subset of its constraints).  This file provides the exact-cone side:
values + witness audits (exact-CS residual at the solver point).  Same
refereed discretization XF=80/na=600/A=3/nb=320, tol=2e-4.

Run with the w3venv python:  ../w3venv/bin/python socp_runs.py
"""
import sys
import numpy as np
import cvxpy as cp

T1 = "/Users/acutis/Projects/brockian-mathematics/research/t1-ceiling"
sys.path.insert(0, T1)
from lp_primal3 import make_cells, cell_cols, tail_cols, TAILB, MMAX  # noqa

DEPTHS = (0.1, 0.2, 0.3, 0.4, 0.5)
C1S = 2 * np.tan(1 / np.sqrt(2)) / (np.sqrt(2) + np.tan(1 / np.sqrt(2)))
RHS44 = 4.0 - 1.0 / C1S


def solve(flags, label="", DMAX=2 * np.pi, i3_tied=True,
          XF=80.0, na=600, nb=320, A=3.0, tol=2e-4):
    lo, hi = make_cells(XF)
    ncell = len(lo); ntail = len(TAILB) + 1; nd = len(DEPTHS)
    has3 = "I3" in flags
    ab = np.linspace(0.0, 1.0, na)
    ao = np.linspace(1.0 + 1e-3, A, nb)
    aa = np.concatenate([ab, ao]); nA = len(aa)
    C = np.array([cell_cols(a, lo, hi) for a in aa])
    Tt = np.array([tail_cols(a, XF) for a in aa])
    Pk = np.array([[4 * np.cosh(2 * np.pi * a * y) ** 2 for y in DEPTHS]
                   for a in aa])
    cosh01 = 4 * np.cosh(2 * np.pi * aa * 0.1) ** 2
    m2 = np.arange(1, MMAX + 1) ** 2
    m1 = np.arange(1, MMAX + 1)

    psi = cp.Variable(MMAX, nonneg=True)
    p = cp.Variable(nd, nonneg=True)
    eta = cp.Variable(ncell)
    tl = cp.Variable(2 * ntail, nonneg=True)
    SO = cp.Variable(nA, nonneg=True)
    SPT = cp.Variable(nA, nonneg=True)          # S_P (+ S_PP if I3)
    X = cp.Variable(nA)
    mu = cp.Variable(ncell, nonneg=True) if has3 else None

    spt_expr = Pk @ p
    if has3:
        spt_expr = spt_expr + cp.multiply(cosh01, C @ mu)
    cons = [
        SO == m2 @ psi + C @ eta + Tt @ (tl[:ntail] - tl[ntail:]),
        SPT == spt_expr,
        m1 @ psi + 2 * cp.sum(p) == 1.0,
        eta >= -1.0,
        SO[:na] + SPT[:na] + X[:na] <= ab + tol,
        SO[:na] + SPT[:na] + X[:na] >= ab - tol,
        SO[na:] + SPT[na:] + X[na:] >= -tol,
        (cp.sum(tl[:ntail - 1]) + cp.sum(tl[ntail:2 * ntail - 1])
         + (tl[ntail - 1] + tl[2 * ntail - 1]) / np.pi ** 2) <= XF ** 2 * 0.9,
        cp.SOC(SO + SPT, cp.vstack([X, SO - SPT]), axis=0),
    ]
    if "I1" in flags:
        cons.append(X[0] >= 0)
    if "I2" in flags:
        cons.append(1.0 + eta <= DMAX * (m1 @ psi))
    if has3 and i3_tied:
        cons.append(mu <= 2.0 * DMAX * cp.sum(p))
    if "I4" in flags:
        w = 2.0 * (1.0 - ab); w[0] *= 0.5; w[-1] *= 0.5
        cons.append(w @ (SO[:na] + SPT[:na] + X[:na]) == float(w @ ab))
    if "I5" in flags:
        cons.append(3 * psi[0] + 4 * (cp.sum(psi[1:]) + cp.sum(p)) >= RHS44)

    prob = cp.Problem(cp.Minimize(psi[0]), cons)
    prob.solve(solver=cp.CLARABEL, verbose=False)
    tag = (f"{label} flags={sorted(flags)}"
           + (" UNTIED" if has3 and not i3_tied else "")
           + (f" DMAX={DMAX:.3g}" if ("I2" in flags or has3) else ""))
    print(f"[{tag}] status = {prob.status}   min psi_1 = "
          f"{prob.value:.7f}" if prob.value is not None else
          f"[{tag}] status = {prob.status}")
    if prob.status in ("optimal", "optimal_inaccurate"):
        so, spt, xv = SO.value, SPT.value, X.value
        cs = np.abs(xv) - 2 * np.sqrt(np.maximum(so, 0) * np.maximum(spt, 0))
        print(f"    psi = {np.round(psi.value, 5)}  p = {np.round(p.value, 5)}"
              f"  exact-CS max resid = {cs.max():+.2e}"
              + (f"  mu mass = {(mu.value @ (hi - lo)):.4f}" if has3 else ""))
    return prob.value


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which in ("all", "main"):
        print("== exact-cone SOCP, ordering A ==")
        solve(set(), "L0 ")
        solve({"I1"}, "L1A")
        solve({"I1", "I2"}, "L2A")
        solve({"I1", "I2", "I3"}, "L3A")
        solve({"I1", "I2", "I3", "I4"}, "L4A")
        solve({"I1", "I2", "I3", "I4", "I5"}, "L5 ")
        print("== exact-cone SOCP, ordering B ==")
        solve({"I5"}, "L1B")
        solve({"I5", "I4"}, "L2B")
        solve({"I5", "I4", "I3"}, "L3B")
        solve({"I5", "I4", "I3", "I2"}, "L4B")
    if which in ("all", "singles"):
        print("== singletons ==")
        solve({"I2"}, "S2 ")
        solve({"I2"}, "S2c", DMAX=1.5)
        solve({"I3"}, "S3 ")
        solve({"I3"}, "S3u", i3_tied=False)
        solve({"I4"}, "S4 ")
        solve({"I1", "I3"}, "S13u", i3_tied=False)
    if which in ("all", "fine"):
        print("== refinement check XF=160/na=1200/A=5/nb=1280 ==")
        solve({"I1"}, "L1A fine", XF=160.0, na=1200, nb=1280, A=5.0)
        solve({"I1", "I2", "I3", "I4", "I5"}, "L5 fine",
              XF=160.0, na=1200, nb=1280, A=5.0)
