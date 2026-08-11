"""T1: cone-linked full-species adversary LP (honest A*, B*).

S_total(alpha) = S_O(alpha) + S_P(alpha) + X(alpha),  X = 2 Re(Z_O conj Z_P),
  |X(alpha)| <= 2 sqrt(S_O S_P)  pointwise  (Cauchy-Schwarz, exact),
  S_O >= 0, S_P >= 0 tautologically.
S_O = on-line structure (multiplicity diag + correlation cells + tails),
S_P = sum_y 4 cosh^2(2 pi a y) p_y   (pair-pair correlations omitted -- noted),
band: S_total(a) = a on [0,1];  Bochner (auto): S_total >= 0 on (1,A].
Outer approx of the cone: |X| <= t S_O + S_P / t,  t in 2^{-3..3}.

This LP's dual = certificates built from: band data equalities + species
structure + CS inequality + integrality -- all unconditionally valid
ingredients at the idealized level. Its value is therefore the natural
candidate for the exact unconditional ceiling of the method.
"""
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix, vstack
from lp_primal3 import make_cells, cell_cols, tail_cols, TAILB, MMAX

TGRID = [2.0**k for k in range(-3, 4)]

def solve_cone(XF=160.0, na=1200, tol=2e-4, Aboch=3.0, nb=None,
               depths=(0.1, 0.2, 0.3, 0.4, 0.5), label="", use_pairs=True):
    lo, hi = make_cells(XF)
    ncell = len(lo); ntail = len(TAILB) + 1
    nd = len(depths) if use_pairs else 0
    ab = np.linspace(0.0, 1.0, na)
    if nb is None: nb = int(2 * (Aboch - 1) * XF) if Aboch else 0
    ao = np.linspace(1.0 + 1e-3, Aboch, nb) if Aboch else np.array([])
    aa = np.concatenate([ab, ao]); nA = len(aa)

    # vars: psi(MMAX) | p_y(nd) | eta(ncell) | tails(2*ntail) | so(nA) | sp(nA) | x(nA)
    n0 = MMAX + nd + ncell + 2 * ntail
    iSO = n0; iSP = n0 + nA; iX = n0 + 2 * nA
    n = n0 + 3 * nA
    iP, iE, iT = MMAX, MMAX + nd, MMAX + nd + ncell

    rows, rl, ru = [], [], []   # sparse rows with lower/upper (build as A_ub twice)
    Aub = lil_matrix((0, n))    # we'll collect via lists of (cols, vals)

    data_rows = []; data_b = []; sense = []  # 'eq' handled separately

    # structure: so_a - [on-line transform](a) = 0   (dense rows)
    S_A = lil_matrix((nA, n)); S_b = np.zeros(nA)
    for i, a in enumerate(aa):
        S_A[i, :MMAX] = np.arange(1, MMAX + 1) ** 2
        S_A[i, iE:iT] = cell_cols(a, lo, hi)
        tc = tail_cols(a, XF)
        S_A[i, iT:iT + ntail] = tc
        S_A[i, iT + ntail:iT + 2 * ntail] = -tc
        S_A[i, iSO + i] = -1.0
    # sp_a - sum 4cosh^2 p = 0
    P_A = lil_matrix((nA, n))
    for i, a in enumerate(aa):
        for k, y in enumerate(depths[:nd]):
            P_A[i, iP + k] = 4 * np.cosh(2 * np.pi * a * y) ** 2
        P_A[i, iSP + i] = -1.0
    # count equality
    C_A = lil_matrix((1, n))
    C_A[0, :MMAX] = np.arange(1, MMAX + 1)
    C_A[0, iP:iE] = 2.0
    A_eq = vstack([S_A, P_A, C_A]).tocsr()
    b_eq = np.concatenate([np.zeros(2 * nA), [1.0]])

    # inequalities
    ub_rows = lil_matrix((2 * na + (nA - na) + 2 * len(TGRID) * nA + 1, n))
    ub_b = np.zeros(ub_rows.shape[0])
    r = 0
    # band: |so+sp+x - a| <= tol
    for i in range(na):
        ub_rows[r, iSO + i] = 1; ub_rows[r, iSP + i] = 1; ub_rows[r, iX + i] = 1
        ub_b[r] = ab[i] + tol; r += 1
        ub_rows[r, iSO + i] = -1; ub_rows[r, iSP + i] = -1; ub_rows[r, iX + i] = -1
        ub_b[r] = -(ab[i] - tol); r += 1
    # Bochner: -(so+sp+x) <= tol
    for i in range(na, nA):
        ub_rows[r, iSO + i] = -1; ub_rows[r, iSP + i] = -1; ub_rows[r, iX + i] = -1
        ub_b[r] = tol; r += 1
    # cone: +-x <= t*so + sp/t
    for t in TGRID:
        for i in range(nA):
            ub_rows[r, iX + i] = 1; ub_rows[r, iSO + i] = -t
            ub_rows[r, iSP + i] = -1.0 / t; ub_b[r] = 0.0; r += 1
            ub_rows[r, iX + i] = -1; ub_rows[r, iSO + i] = -t
            ub_rows[r, iSP + i] = -1.0 / t; ub_b[r] = 0.0; r += 1
    # tail budget
    ub_rows[r, iT:iT + ntail - 1] = 1.0
    ub_rows[r, iT + ntail:iT + 2 * ntail - 1] = 1.0
    ub_rows[r, iT + ntail - 1] = 1 / np.pi ** 2
    ub_rows[r, iT + 2 * ntail - 1] = 1 / np.pi ** 2
    ub_b[r] = XF ** 2 * 0.9; r += 1
    A_ub = ub_rows.tocsr()

    bounds = ([(0, None)] * (MMAX + nd) + [(-1.0, None)] * ncell
              + [(0, None)] * (2 * ntail)
              + [(0, None)] * nA          # so >= 0 (tautology)
              + [(0, None)] * nA          # sp >= 0
              + [(None, None)] * nA)      # x free
    c = np.zeros(n); c[0] = 1.0
    res = linprog(c, A_ub=A_ub, b_ub=ub_b, A_eq=A_eq, b_eq=b_eq,
                  bounds=bounds, method="highs")
    if res.success:
        psi = res.x[:MMAX]; pd = res.x[iP:iE]
        xmax = np.max(np.abs(res.x[iX:iX + nA])) if nA else 0
        print(f"[{label}] min psi_1 = {res.fun:.6f}  psi={np.round(psi, 5)}\n"
              f"    pair masses {tuple(depths[:nd])} = {np.round(pd, 6)}   "
              f"max|X| = {xmax:.4f}", flush=True)
    else:
        print(f"[{label}] FAILED: {res.message}", flush=True)
    return res

if __name__ == "__main__":
    import sys
    which = sys.argv[1] if len(sys.argv) > 1 else "cone"
    if which == "cone":
        solve_cone(XF=160., na=1200, Aboch=3.0, label="cone-B* XF=160 A=3")
    elif which == "coneA":
        solve_cone(XF=160., na=1200, Aboch=None, nb=0, label="cone-A* XF=160")
    elif which == "depthsweep":
        for dep in [(0.1,), (0.1, 0.2, 0.3), (0.1, 0.2, 0.3, 0.4, 0.5),
                    (0.1, 0.2, 0.3, 0.4, 0.5, 0.65, 0.8)]:
            solve_cone(XF=160., na=1200, Aboch=3.0, depths=dep,
                       label=f"cone-B* maxdepth={dep[-1]}")
