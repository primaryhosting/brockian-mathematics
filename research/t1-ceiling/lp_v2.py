"""T1 v2: certificate-side (dual) LPs + tolerance-primal sandwich.

DUAL-A (Montgomery class): value_A = min int r(x)(1-F(x))dx over
    r even, rhat supported [-1,1], r(0)=1, r(x)>=0 on R.
  D2 <= 1 + value_A;  ceiling_A = 2 - (1+value_A).  Expect 0.672501.

DUAL-B (Cohn-Elkies / doubly-positive class): value_B = min over
    R even with Rhat on [-B,B], R(0)=1, R(x)>=0 on R, Rhat(alpha)<=0 for
    1<|alpha|<=B, of  band-read = Rhat(0) + 2 int_0^1 Rhat(alpha) alpha dalpha
    - ... careful: D2 <= band-read; ceiling_B = 2 - band-read.
  Valid ONLY for on-line configurations. Expect 0.68185 (paper Rem 1.1)?

DUAL-C: DUAL-B + pair-robustness constraints at scaled depths y:
    R(0) + R(2iy) >= 2 * (paper-charge?) ... exact form derived from the primal
    pair column: pair (m=1, depth y): count 2, S-profile 4cosh^2(2 pi a y).
    Dual feasibility for that column:
        int Rhat(a) 4 cosh^2(2 pi a y) da >= 4 * mu2   [mu2 = count multiplier]
    i.e. 2(R(0) + R(2iy)) >= 4 mu2, where the double (y=0) column gives
        equality structure 8 mu ... we just add columns in the primal instead.

PRIMAL (tolerant): adversary LP as before with band tolerance; sandwich.
"""
import numpy as np
from scipy.optimize import linprog

def dual_lp(B=4.0, na_in=400, na_out=1200, nx=6000, Xmax=40.0, ce=True,
            depth_constraints=(), verbose=True):
    """Variables rho_i = Rhat(alpha_i) on [0,B] (even function, half-line rep).
    R(x) = 2 * sum_i w_i rho_i cos(2 pi alpha_i x); R(0)=1;
    minimize band-read = 2*sum_{alpha_i<=1} w_i rho_i * ???  -- careful:
      band-read for zeta: int_{-1}^{1} Rhat(a) (delta_0(a)+|a|) da
                        = Rhat(0) + 2 int_0^1 Rhat(a) a da.
      Rhat(0) is a point value: on the grid, rho at alpha=0.
    """
    a_in = np.linspace(0.0, 1.0, na_in + 1)
    w_in = np.full(na_in + 1, 1.0 / na_in); w_in[0] *= 0.5; w_in[-1] *= 0.5
    if ce:
        a_out = np.linspace(1.0, B, na_out + 1)[1:]
        w_out = np.full(na_out, (B - 1.0) / na_out)
        alphas = np.concatenate([a_in, a_out])
        weights = np.concatenate([w_in, w_out])
    else:
        alphas, weights = a_in, w_in
    n = len(alphas)

    xs = np.linspace(0.0, Xmax, nx + 1)
    cosm = np.cos(2 * np.pi * np.outer(xs, alphas))     # nx+1 x n

    A_ub, b_ub = [], []
    # -R(x_j) <= 0
    for j in range(nx + 1):
        A_ub.append(-2 * weights * cosm[j]); b_ub.append(0.0)
    # Rhat(alpha) <= 0 outside band
    bounds = []
    for i, a in enumerate(alphas):
        bounds.append((None, 0.0) if a > 1.0 else (None, None))
    # depth constraints: R(0) + R(2iy) >= c_y  (from pair columns; c_y set by
    # caller as 2*mu2 with mu2 the count-multiplier -- for the pure obstruction
    # demo we impose the SIGN-ROBUST version R(0)+R(2iy) >= 0):
    for (y, cy) in depth_constraints:
        coshv = np.cosh(4 * np.pi * alphas * y)
        row = -(2 * weights * (1.0 + coshv))            # -(R(0)+R(2iy)) hmm:
        # R(0) = 2 sum w rho;  R(2iy) = 2 sum w rho cosh(4 pi a y)
        A_ub.append(row); b_ub.append(-cy)
    # normalization R(0) = 1
    A_eq = [2 * weights]; b_eq = [1.0]

    # objective: band-read = Rhat(0) + 2 sum_{a<=1} w rho a
    c = np.zeros(n)
    c[0] += 1.0                    # Rhat(0) point value = rho_0
    band = alphas <= 1.0
    c[band] += 2 * weights[band] * alphas[band]

    res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                  A_eq=np.array(A_eq), b_eq=np.array(b_eq),
                  bounds=bounds, method="highs")
    if verbose:
        tag = "CE" if ce else "Montgomery"
        if depth_constraints: tag += f"+depths{[d[0] for d in depth_constraints]}"
        if res.success:
            print(f"[DUAL {tag}] D2-bound = {res.fun:.6f}   "
                  f"ceiling = {2-res.fun:.6f}")
        else:
            print(f"[DUAL {tag}] FAILED: {res.message}")
    return res, alphas, weights

if __name__ == "__main__":
    print("DUAL-A (Montgomery, rhat support [0,1], r>=0):  expect 1.32750 / 0.67250")
    dual_lp(ce=False)
    print()
    print("DUAL-B (Cohn-Elkies doubly-positive, B=4):")
    r, al, w = dual_lp(ce=True, B=4.0)
    print()
    print("DUAL-B (B=2.5) and (B=6) support-sensitivity:")
    dual_lp(ce=True, B=2.5)
    dual_lp(ce=True, B=6.0, na_out=1600)
