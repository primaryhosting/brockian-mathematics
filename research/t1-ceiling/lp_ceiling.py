"""T1: adversary LPs for the bandwidth-1 ceiling.

Per-N species model (derived from paper Secs 4-5, Rem 5.10, 7.5(b)):
  on-line distinct point, multiplicity m: count m, S_emp(alpha) diagonal m^2
  off-line pair {rho,1-rhobar}, mult m, scaled depth y: count 2m,
      S_emp internal contribution 4 m^2 cosh^2(2 pi alpha y)   (>=0 always;
      y=0 identical to an on-line double: 4m^2)
  correlations between distinct sites: background 1 + eta(x), eta >= -1,
      contributing (via Fourier) delta_0 + 2 int eta cos(2 pi alpha x) dx.

Zeta band data (unconditional, Montgomery/BGSTB as packaged by the paper):
  S(alpha) = delta_0(alpha) + |alpha| on [-1,1].
After cancelling delta_0 (background), band equality for alpha in [0,1]:
  sum_m m^2 psi_m + sum_k 4 cosh^2(2 pi alpha y_k) p_k
      + 2h sum_j eta_j cos(2 pi alpha x_j) = alpha .
Count: sum_m m psi_m + 2 sum_k p_k = 1.
Objective: minimize psi_1  (= ceiling on certifiable simple on-line fraction).

Variant A: equalities only                       -> expect 1 - 0.32750 = 0.67250
Variant B: + S(alpha) >= 0 for alpha in (1, A]   -> paper's Remark 1.1? 0.68185?
Variant C: B + deep-pair species                 -> does the ceiling fall back?
"""
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix

# ---------------- grids ----------------
X, h = 16.0, 0.02                    # x-grid for eta
xg = np.arange(h / 2, X, h)
NA_BAND = 201
ab = np.linspace(0.0, 1.0, NA_BAND)  # band alphas (equalities)
MMAX = 5                             # on-line multiplicities 1..MMAX

def build_and_solve(bochner_A=None, n_boch=400, depths=(), verbose=True,
                    band_tol=0.0):
    """Variables: psi_1..psi_MMAX, p_k (pairs per depth), eta_j.
    band_tol>0 turns band equalities into +-tol inequalities (discretization
    robustness check)."""
    npsi, npair, neta = MMAX, len(depths), len(xg)
    n = npsi + npair + neta
    iP = npsi                      # pair vars start
    iE = npsi + npair              # eta vars start

    cos_be = np.cos(2 * np.pi * np.outer(ab, xg))          # band x eta
    # band equalities: sum m^2 psi + sum 4cosh^2 p + 2h eta.cos = alpha
    Aeq = np.zeros((NA_BAND + 1, n))
    beq = np.zeros(NA_BAND + 1)
    for i, a in enumerate(ab):
        Aeq[i, :npsi] = [(m + 1)**2 for m in range(MMAX)][:npsi]
        Aeq[i, :npsi] = [(m)**2 for m in range(1, MMAX + 1)]
        for k, y in enumerate(depths):
            Aeq[i, iP + k] = 4 * np.cosh(2 * np.pi * a * y)**2
        Aeq[i, iE:] = 2 * h * cos_be[i]
        beq[i] = a
    # count equality
    Aeq[NA_BAND, :npsi] = np.arange(1, MMAX + 1)
    Aeq[NA_BAND, iP:iE] = 2.0
    beq[NA_BAND] = 1.0

    A_ub, b_ub = [], []
    # eta >= -1  ->  -eta <= 1 (use bounds instead)
    bounds = [(0, None)] * (npsi + npair) + [(-1.0, None)] * neta

    if bochner_A is not None:
        abo = np.linspace(1.0 + 1e-3, bochner_A, n_boch)
        cos_bo = np.cos(2 * np.pi * np.outer(abo, xg))
        for i, a in enumerate(abo):
            row = np.zeros(n)
            row[:npsi] = np.arange(1, MMAX + 1)**2
            for k, y in enumerate(depths):
                row[iP + k] = 4 * np.cosh(2 * np.pi * a * y)**2
            row[iE:] = 2 * h * cos_bo[i]
            A_ub.append(-row)      # -(S(alpha)) <= 0
            b_ub.append(0.0)

    c = np.zeros(n); c[0] = 1.0    # minimize psi_1

    if band_tol > 0:
        for i in range(Aeq.shape[0] - 1):
            A_ub.append(Aeq[i].copy());  b_ub.append(beq[i] + band_tol)
            A_ub.append(-Aeq[i].copy()); b_ub.append(-(beq[i] - band_tol))
        Aeq2, beq2 = Aeq[-1:], beq[-1:]
    else:
        Aeq2, beq2 = Aeq, beq

    res = linprog(c, A_ub=np.array(A_ub) if A_ub else None,
                  b_ub=np.array(b_ub) if b_ub else None,
                  A_eq=Aeq2, b_eq=beq2, bounds=bounds, method="highs")
    if verbose:
        tag = f"Bochner A={bochner_A}, depths={list(depths)}, tol={band_tol}"
        if not res.success:
            print(f"[{tag}] INFEASIBLE/{res.status}: {res.message}")
            return res
        psi = res.x[:npsi]; pr = res.x[iP:iE]
        print(f"[{tag}]")
        print(f"  min psi_1 (ceiling)      = {res.fun:.6f}")
        print(f"  psi (m=1..{MMAX})           = {np.round(psi,5)}")
        if npair:
            print(f"  pair masses per depth    = {np.round(pr,6)}")
        d2 = np.dot(np.arange(1, MMAX+1)**2, psi) + 4*np.sum(pr)  # crude (y~0 part)
        print(f"  delta used (D2-1 proxy)  = {d2-1:.6f}")
    return res

if __name__ == "__main__":
    print("=" * 70)
    print("VARIANT A: band equalities only (relaxed adversary)")
    print("  expect ceiling -> 2 - 1/c1* = 0.672501")
    build_and_solve(bochner_A=None)

    print()
    print("=" * 70)
    print("VARIANT B: + spectral positivity S(alpha)>=0, alpha in (1,4] (on-line)")
    build_and_solve(bochner_A=4.0)

    print()
    print("=" * 70)
    print("VARIANT C: B + off-line pair species at scaled depths")
    build_and_solve(bochner_A=4.0, depths=(0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.35))
