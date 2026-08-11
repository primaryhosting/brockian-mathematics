"""T1 primal v2: adversary LP with exact analytic tail columns.

Tail machinery: for x > X the correlation density is 1 + sum_b c_b g_b(x),
  g_b(x) = cos(2 pi b x)/x^2  (b in TAILB)  and  gF(x) = -F(x) (Fejer).
Exact transforms via  CI(w) = int_X^inf cos(w x)/x^2 dx
                            = cos(wX)/X - w (pi/2 - Si(wX))   (w >= 0, even in w).
  2 int_X^inf g_b cos(2 pi a x) dx = CI(2pi|a-b|) + CI(2pi(a+b))
  2 int_X^inf (-F) cos(2 pi a x) dx
      = -(1/pi^2) [ CI(2pi a) - (CI(2pi|a-1|) + CI(2pi(a+1)))/2 ]
Positivity for x>X: 1 - (sum|c_b| + |c_F|/pi^2)/X^2 >= 0  (conservative).
"""
import numpy as np
from scipy.optimize import linprog
from scipy.special import sici

X = 20.0
TAILB = (0.0, 0.25, 0.5, 0.75, 1.0)
MMAX = 5

def CI(w):
    w = np.abs(w)
    out = np.empty_like(np.atleast_1d(w), dtype=float)
    w1 = np.atleast_1d(w)
    small = w1 < 1e-14
    out[small] = 1.0 / X
    si, _ = sici(w1[~small] * X)
    out[~small] = np.cos(w1[~small] * X) / X - w1[~small] * (np.pi / 2 - si)
    return out if np.ndim(w) else float(out[0])

def tail_cols(a):
    """transforms of tail basis at frequency a (scalar): returns array len(TAILB)+1."""
    cols = [CI(2*np.pi*abs(a - b)) + CI(2*np.pi*(a + b)) for b in TAILB]
    colF = -(1/np.pi**2) * (CI(2*np.pi*a)
                            - 0.5*(CI(2*np.pi*abs(a-1)) + CI(2*np.pi*(a+1))))
    return np.array(cols + [colF])

def solve(h=0.02, na=201, tol=2e-4, bochner_A=None, nb=400, depths=(),
          label="", mt_check=False):
    xg = np.arange(h/2, X, h)
    ab = np.linspace(0.0, 1.0, na)
    ntail = len(TAILB) + 1
    npair, neta = len(depths), len(xg)
    # vars: psi(MMAX), pairs, eta, tail c+ (ntail), tail c- (ntail)
    n = MMAX + npair + neta + 2*ntail
    iP, iE, iT = MMAX, MMAX+npair, MMAX+npair+neta

    def srow(a):
        row = np.zeros(n)
        row[:MMAX] = np.arange(1, MMAX+1)**2
        for k, y in enumerate(depths):
            row[iP+k] = 4*np.cosh(2*np.pi*a*y)**2
        row[iE:iT] = 2*h*np.cos(2*np.pi*a*xg)
        tc = tail_cols(a)
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
    # tail positivity: sum(c+ + c-) for cos-tails + (cF+ + cF-)/pi^2 <= X^2 - eps
    row = np.zeros(n)
    row[iT:iT+ntail-1] = 1.0; row[iT+ntail:-1] = 1.0
    row[iT+ntail-1] = 1/np.pi**2; row[-1] = 1/np.pi**2
    A_ub.append(row); b_ub.append(X**2 * 0.9)

    A_eq = np.zeros((1, n))
    A_eq[0, :MMAX] = np.arange(1, MMAX+1)
    A_eq[0, iP:iE] = 2.0
    b_eq = [1.0]
    bounds = ([(0, None)]*(MMAX+npair) + [(-1.0, None)]*neta
              + [(0, None)]*(2*ntail))
    c = np.zeros(n); c[0] = 1.0

    res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                  A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
    if res.success:
        psi = res.x[:MMAX]; pr = res.x[iP:iE]
        msg = f"[{label}] min psi_1 = {res.fun:.6f}  psi={np.round(psi,5)}"
        if npair: msg += f"\n    pairs(depths {depths}) = {np.round(pr,7)}"
        print(msg)
    else:
        print(f"[{label}] FAILED: {res.message}")
    return res

if __name__ == "__main__":
    import sys
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which in ("all", "A"):
        print("--- A (band only): expect -> 0.672501 ---")
        for tol in (1e-3, 5e-4, 2e-4):
            solve(tol=tol, label=f"A tol={tol}")
    if which in ("all", "B"):
        print("--- B (+S>=0 on (1,3]): candidate for Rem 1.1's 0.68185 ---")
        for tol in (1e-3, 5e-4, 2e-4):
            solve(tol=tol, bochner_A=3.0, label=f"B tol={tol}")
    if which in ("all", "C"):
        print("--- C (B + off-line pairs): does the ceiling collapse back? ---")
        for dep in [(0.1,), (0.1, 0.2), (0.1, 0.2, 0.3),
                    (0.1, 0.2, 0.3, 0.4, 0.5)]:
            solve(tol=5e-4, bochner_A=3.0, depths=dep,
                  label=f"C maxdepth={dep[-1]}")
