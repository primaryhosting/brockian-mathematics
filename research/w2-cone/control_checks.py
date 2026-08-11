"""W2 controls for the exact-cone verdict.

CONTROL P (positive): the genuine GUE / all-simple pseudo-configuration
  psi_1 = 1, eta(x) = -sinc^2(x) (= -(sin pi x / pi x)^2), tail basis -F(x)
  with coefficient 1 (the model's colF tail column is EXACTLY the transform
  of -F on [XF, inf), by construction in lp_primal3.tail_cols).
  Continuum identity: S_O(a) = 1 - (1-|a|)_+ = |a| on [-1,1], = 1 beyond.
  The model must ACCEPT it within its band tolerance.  This validates the
  encoding (cells, tails, band rows, out-of-band S_O >= 0).

CONTROL N (negative): pure doubles psi_2 = 1/2, no pairs.  The task brief
  asserts this "IS exactly feasible" -- it is NOT, provably:
  with p = 0 the exact cone forces X = 0, so S_O(a) = a on [0,1] with
  on-line diagonal sum m^2 psi_m = 4 * (1/2) = 2.  But for ANY k >= 0 with
  supp khat in [-1,1] and any density eta >= -1 (nu >= 0),
      sum m^2 psi_m * k(0)  <=  khat(0) + int_{-1}^{1} |a| khat(a) da,
  (pair with khat, use int k d nu >= -khat(0) from eta >= -1).  The Fejer
  window k = sinc^2 (khat = triangle) gives the bound 4/3 < 2; the
  Montgomery-Taylor optimal window gives M = 1/c1* = 1.3274992 < 2.
  So pure doubles is band-infeasible in the continuum, and the grid LP must
  report infeasible.  (Same certificate shows the SS 7.5(b) matrix-extremal
  psi_1 = 2/3, psi_2 = 1/6, with sum m^2 psi = 4/3 > 1.3274992, is also
  marginally band-infeasible -- consistent with V_A = 0.6725 > 2/3.)

  The CORRECT exactly-feasible on-line control at the LP's own optimum is
  psi_1 = 0.6725, psi_2 = 0.1637 (sum m^2 psi = 1.32750 = M, saturating
  Montgomery-Taylor) -- which is what Variant A returns.

Run with system python3 (scipy only) or the venv python.
"""
import sys
import numpy as np
from scipy.optimize import linprog
from scipy.integrate import quad

T1 = "/Users/acutis/Projects/brockian-mathematics/research/t1-ceiling"
sys.path.insert(0, T1)
from lp_primal3 import make_cells, cell_cols, tail_cols, TAILB, MMAX  # noqa: E402


def sinc2(x):
    x = np.asarray(x, dtype=float)
    out = np.ones_like(x)
    nz = np.abs(x) > 1e-300
    out[nz] = (np.sin(np.pi * x[nz]) / (np.pi * x[nz])) ** 2
    return out


def control_P(XF=80.0, na=600, Aboch=3.0, nb=320, tol=2e-4):
    print("== CONTROL P: GUE all-simple config (psi_1 = 1, eta = -sinc^2, "
          "tail = -F) ==")
    lo, hi = make_cells(XF)
    ntail = len(TAILB) + 1
    # cell values = exact cell averages of -sinc^2 (piecewise-constant eta)
    eta = np.array([-quad(lambda x: sinc2(x), a, b, limit=200)[0] / (b - a)
                    for a, b in zip(lo, hi)])
    assert np.all(eta >= -1.0 - 1e-12)
    tails = np.zeros(2 * ntail)
    tails[ntail - 1] = 1.0          # +block colF coefficient: tail density -F
    ab = np.linspace(0.0, 1.0, na)
    ao = np.linspace(1.0 + 1e-3, Aboch, nb)

    def SO(a):
        tc = tail_cols(a, XF)
        return (1.0                      # sum m^2 psi_m, psi_1 = 1
                + float(cell_cols(a, lo, hi) @ eta)
                + float(tc @ tails[:ntail]) - float(tc @ tails[ntail:]))

    band = np.array([SO(a) - a for a in ab])
    oob = np.array([SO(a) for a in ao])
    print(f"  cells: {len(lo)} exact cell-averages of -sinc^2; "
          f"min eta = {eta.min():.6f} (>= -1)")
    print(f"  band residual max |S_O(a) - a| on {na} pts = "
          f"{np.abs(band).max():.3e}  (raw cell-averaging of the analytic "
          f"eta; pure discretization error)")
    print(f"  out-of-band (1,{Aboch}]: min S_O = {oob.min():.6f} "
          f"(continuum value 1; must be >= 0)")
    # Fair test of the MODEL: eta/tails are free variables -- LP-polish them
    # (psi_1 = 1 fixed, p = 0) and minimize the band sup-residual t.
    ncell = len(lo)
    nv = ncell + 2 * ntail + 1       # eta, tails, t
    A_ub, b_ub = [], []
    for a in ab:
        cc = cell_cols(a, lo, hi); tc = tail_cols(a, XF)
        row = np.concatenate([cc, tc, -tc, [-1.0]])
        A_ub.append(row);  b_ub.append(a - 1.0)
        A_ub.append(np.concatenate([-cc, -tc, tc, [-1.0]]))
        b_ub.append(-(a - 1.0))
    for a in ao:
        cc = cell_cols(a, lo, hi); tc = tail_cols(a, XF)
        A_ub.append(np.concatenate([-cc, -tc, tc, [0.0]])); b_ub.append(1.0)
    row = np.zeros(nv)
    row[ncell:ncell + ntail - 1] = 1.0
    row[ncell + ntail:ncell + 2 * ntail - 1] = 1.0
    row[ncell + ntail - 1] = 1 / np.pi ** 2
    row[ncell + 2 * ntail - 1] = 1 / np.pi ** 2
    A_ub.append(row); b_ub.append(XF ** 2 * 0.9)
    bounds = ([(-1.0, None)] * ncell + [(0, None)] * (2 * ntail)
              + [(0, None)])
    cvec = np.zeros(nv); cvec[-1] = 1.0
    res = linprog(cvec, A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                  bounds=bounds, method="highs")
    tstar = res.fun if res.status == 0 else np.inf
    print(f"  LP-polished (eta free, psi_1 = 1 fixed): min sup-band-residual "
          f"t* = {tstar:.3e}  (model tol = {tol:.0e})")
    ok = tstar <= tol and oob.min() >= 0
    print(f"  CONTROL P {'PASS' if ok else 'FAIL'}: model "
          f"{'accepts' if ok else 'rejects'} the genuine all-simple GUE "
          f"configuration\n")
    return ok


def montgomery_certificates():
    print("== CONTROL N certificates: upper bounds on sum m^2 psi_m from "
          "band data + nu >= 0 ==")
    # Fejer window k = sinc^2: khat = (1-|a|)_+, k(0) = 1, khat(0) = 1
    I = quad(lambda a: abs(a) * (1 - abs(a)), -1, 1)[0]
    fejer = (1.0 + I) / 1.0
    print(f"  Fejer window:  sum m^2 psi <= khat(0) + int |a| khat = "
          f"{fejer:.7f}  (= 4/3)")
    c1 = 2 * np.tan(1 / np.sqrt(2)) / (np.sqrt(2) + np.tan(1 / np.sqrt(2)))
    print(f"  Montgomery-Taylor optimum: sum m^2 psi <= 1/c1* = {1/c1:.7f}")
    print(f"  pure doubles needs sum m^2 psi = 2   > {fejer:.4f}  -> "
          f"INFEASIBLE (proof, continuum)")
    print(f"  SS7.5(b) matrix-extremal (2/3, 1/6) needs 4/3 = 1.3333 "
          f"> {1/c1:.7f} -> also band-infeasible (marginally)\n")
    return fejer, 1 / c1


def control_N(XF=80.0, na=600, tol=2e-4, Aboch=3.0, nb=320):
    print("== CONTROL N: grid LP feasibility for pure doubles "
          "(psi_2 = 1/2, p = 0 -> S_P = 0, X = 0) ==")
    lo, hi = make_cells(XF)
    ncell = len(lo); ntail = len(TAILB) + 1
    n = ncell + 2 * ntail            # psi fixed, only eta + tails free
    ab = np.linspace(0.0, 1.0, na)
    ao = np.linspace(1.0 + 1e-3, Aboch, nb)
    diag = 4.0 * 0.5                 # sum m^2 psi_m = 2
    A_ub, b_ub = [], []
    for a in ab:                     # |diag + T eta + tails - a| <= tol
        cc = cell_cols(a, lo, hi); tc = tail_cols(a, XF)
        row = np.concatenate([cc, tc, -tc])
        A_ub.append(row);  b_ub.append(a - diag + tol)
        A_ub.append(-row); b_ub.append(-(a - diag - tol))
    for a in ao:                     # S_O >= 0 out of band
        cc = cell_cols(a, lo, hi); tc = tail_cols(a, XF)
        A_ub.append(-np.concatenate([cc, tc, -tc])); b_ub.append(diag)
    row = np.zeros(n)
    row[ncell:ncell + ntail - 1] = 1.0
    row[ncell + ntail:n - 1] = 1.0
    row[ncell + ntail - 1] = 1 / np.pi ** 2
    row[n - 1] = 1 / np.pi ** 2
    A_ub.append(row); b_ub.append(XF ** 2 * 0.9)
    bounds = [(-1.0, None)] * ncell + [(0, None)] * (2 * ntail)
    res = linprog(np.zeros(n), A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                  bounds=bounds, method="highs")
    print(f"  linprog status: {res.status} ({res.message.strip()})")
    infeas = (res.status == 2
              or "infeasible" in str(res.message).lower())
    print(f"  CONTROL N {'PASS' if infeas else 'FAIL'}: grid LP is "
          f"{'INFEASIBLE, as the continuum certificate demands' if infeas else 'unexpectedly feasible -- INVESTIGATE'}")
    if infeas:
        print("  => the task brief's premise that pure doubles is exactly "
              "feasible is REFUTED (Fejer/Montgomery-Taylor dual above);")
        print("     the model rejecting it is CORRECT behaviour, not a model "
              "bug.\n")
    return infeas


if __name__ == "__main__":
    okP = control_P()
    montgomery_certificates()
    okN = control_N()
    print(f"controls: P(accept genuine GUE) = {'PASS' if okP else 'FAIL'}, "
          f"N(reject pure doubles, with proof) = {'PASS' if okN else 'FAIL'}")
