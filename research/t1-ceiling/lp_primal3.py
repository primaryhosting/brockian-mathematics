"""T1 primal v3: exact cell-integral columns, scalable far field.

sigma = D2*delta_0 + nu, nu >= 0 on (0,inf) (even ext), must satisfy
  sigmahat(alpha) = delta_0(alpha) + |alpha|  on the band [0,1].
nu = background dx (gives delta_0) + density eta (cellwise, >= -1) [+ implicit
atoms via tall cells]. Exact transform of cell [x0,x1] with unit density:
  2 int_{x0}^{x1} cos(2 pi a x) dx = [sin(2 pi a x1) - sin(2 pi a x0)]/(pi a).
Tail beyond XF: basis cos(2 pi b x)/x^2 and -F(x), exact via Si.

Species: on-line multiplicity m (m<=5), off-line pairs at depths y (variant C).
Variant B/C add S(alpha) >= 0 on (1, A].
"""
import numpy as np
from scipy.optimize import linprog
from scipy.special import sici

MMAX = 5
TAILB = tuple(np.arange(0, 1.01, 0.125))

def make_cells(XF):
    edges = [np.arange(0, 4, 0.02), np.arange(4, 40, 0.1),
             np.arange(40, XF + 1e-9, 0.25)]
    e = np.unique(np.concatenate(edges + [[XF]]))
    return e[:-1], e[1:]

def cell_cols(a, lo, hi):
    if a < 1e-12:
        return 2.0 * (hi - lo)
    return (np.sin(2*np.pi*a*hi) - np.sin(2*np.pi*a*lo)) / (np.pi*a)

def CI(w, XF):
    w = abs(w)
    if w < 1e-14:
        return 1.0 / XF
    si, _ = sici(w * XF)
    return np.cos(w * XF)/XF - w*(np.pi/2 - si)

def tail_cols(a, XF):
    cols = [CI(2*np.pi*abs(a-b), XF) + CI(2*np.pi*(a+b), XF) for b in TAILB]
    colF = -(1/np.pi**2)*(CI(2*np.pi*a, XF)
                          - 0.5*(CI(2*np.pi*abs(a-1), XF) + CI(2*np.pi*(a+1), XF)))
    return np.array(cols + [colF])

def solve(XF=80.0, na=251, tol=2e-4, bochner_A=None, nb=400, depths=(),
          label="", amax=1.0):
    lo, hi = make_cells(XF)
    ncell = len(lo)
    ntail = len(TAILB) + 1
    npair = len(depths)
    n = MMAX + npair + ncell + 2*ntail
    iP, iE, iT = MMAX, MMAX+npair, MMAX+npair+ncell

    ab = np.linspace(0.0, amax, na)

    def srow(a):
        row = np.zeros(n)
        row[:MMAX] = np.arange(1, MMAX+1)**2
        for k, y in enumerate(depths):
            row[iP+k] = 4*np.cosh(2*np.pi*a*y)**2
        row[iE:iT] = cell_cols(a, lo, hi)
        tc = tail_cols(a, XF)
        row[iT:iT+ntail] = tc
        row[iT+ntail:] = -tc
        return row

    A_ub, b_ub = [], []
    for a in ab:
        r = srow(a)
        A_ub.append(r);  b_ub.append(a + tol)
        A_ub.append(-r); b_ub.append(-(a - tol))
    if bochner_A is not None:
        for a in np.linspace(1.0+1e-3, bochner_A, nb):
            A_ub.append(-srow(a)); b_ub.append(tol)
    # tail positivity budget
    row = np.zeros(n)
    row[iT:iT+ntail-1] = 1.0; row[iT+ntail:-1] = 1.0
    row[iT+ntail-1] = 1/np.pi**2; row[-1] = 1/np.pi**2
    A_ub.append(row); b_ub.append(XF**2 * 0.9)

    A_eq = np.zeros((1, n))
    A_eq[0, :MMAX] = np.arange(1, MMAX+1)
    A_eq[0, iP:iE] = 2.0
    b_eq = [1.0]
    bounds = ([(0, None)]*(MMAX+npair) + [(-1.0, None)]*ncell
              + [(0, None)]*(2*ntail))
    c = np.zeros(n); c[0] = 1.0

    res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                  A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
    if res.success:
        psi = res.x[:MMAX]; pr = res.x[iP:iE]
        msg = f"[{label}] min psi_1 = {res.fun:.6f}  psi={np.round(psi,5)}"
        if npair: msg += f"\n    pair masses {depths} -> {np.round(pr,7)}"
        print(msg, flush=True)
    else:
        print(f"[{label}] FAILED: {res.message}", flush=True)
    return res

if __name__ == "__main__":
    import sys
    which = sys.argv[1] if len(sys.argv) > 1 else "A"
    if which == "A":
        for XF in (40.0, 80.0, 160.0):
            solve(XF=XF, tol=2e-4, label=f"A XF={XF}")
    elif which == "B":
        for XF in (80.0, 160.0):
            solve(XF=XF, tol=2e-4, bochner_A=3.0, label=f"B XF={XF}")
    elif which == "C":
        for dep in [(0.1,), (0.1, 0.25), (0.1, 0.25, 0.4), (0.1, 0.25, 0.4, 0.6)]:
            solve(XF=80.0, tol=2e-4, bochner_A=3.0, depths=dep,
                  label=f"C maxdepth={dep[-1]}")
