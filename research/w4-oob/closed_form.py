"""W4 closed-form-family certificate for the doubly-positive one-delta value
[DATA-1DELTA, continuum, basis-free] -- the R2 upgrade vehicle.

THE CERTIFICATE CHAIN (derived + calibrated in this file; the only inputs
are band data, x-space positivity of the correlation, oob spectral
positivity, the count identity, and integer multiplicities m <= 5):

  Let u: [0, T] -> C (T > 1), h(x) = int u(t) e^{2 pi i t x} dt,
  K(x) = |h(x)|^2  >= 0 on R  STRUCTURALLY (no pointwise check needed --
  this is the whole design: Referee B's round-1 kill was a kernel whose
  claimed global nonnegativity was a finite check; here nonnegativity is an
  identity), and rho(alpha) = Re int u(t) conj(u(t - alpha)) dt, the
  (automatically even) spectral density of K, supported in [-T, T].

  For ANY configuration in the one-delta class (species psi_m >= 0, m<=5,
  correlation density eta >= -1, NO off-line pairs -- the on-line-adversary
  scope of the refereed V_B numbers; pair scope measured separately below)
  satisfying band equality S(alpha) = |alpha| on [-1,1] and S(alpha) >= 0
  for 1 < |alpha| <= T:

    D2 * R + int K eta_even  =  int S d rho  <=  int_{|a|<=1} |a| rho da
  provided  rho(alpha) <= 0 on (1, T]   (the discarded oob term has sign
  rho * S <= 0), where R = int rho = |int u|^2, and
    int K eta_even >= - int_R K = -rho(0) = -int |u|^2   (K >= 0, eta >= -1).
  Hence the BUDGET:   D2 <= (J + G) / R,
    J := int_{|a|<=1} |a| rho(alpha) da,  G := rho(0).
  With the count sum m psi_m = 1 and integrality (secant multiplier mu_c),
    psi_1 >= min(1 + R, 2R) - J - G      [reduced costs r_m = delta_{m1}
    + m^2 R - mu_c m >= 0 for m = 1..5, checked numerically below].
  Normalizing R = 1 (scale freedom):  psi_1 >= 2 - (J + G).

  CALIBRATION (gate): u = Montgomery-Taylor cos(sqrt2 (t - 1/2)) on [0,1]
  (rho = 0 beyond |alpha| = 1) must give 2 - (J+G) = V_A = 0.6725007.

  COMPLETENESS NOTE (interpretation only, not needed for validity): by the
  Krein/Akhiezer-Fejer-Riesz factorization, EVERY K >= 0 with spectrum in
  [-T, T] is |h|^2 with supp uhat in [0, T]; so the family sweeps the whole
  T-truncated dual cone, and its sup is the true certificate ceiling of
  this regime at spectral reach T.  (First-unjustified-step register W4-2:
  the factorization is cited, not re-proved here; no downstream number
  depends on it.)

  WHY COMPLEX u: real symmetric windows cannot carry negative mass on
  (1, T] without a positive "speck" near the support edge (the wing-wing
  autocorrelation of a real wing is positive, graveyard entry G-W4-1);
  the phase of u is the degree of freedom that evades this.

OUTPUT: a certified continuum lower bound for the doubly-positive
on-line-adversary value (the Remark 1.1 regime), verified a posteriori:
rho <= 0 on (1, T] on a dense grid with an exact piecewise-cubic argument
(rho of piecewise-linear u), all integrals re-evaluated at 4x resolution.
"""
import sys
import numpy as np
from scipy.optimize import minimize

VA = 2 - (np.sqrt(2) + np.tan(1 / np.sqrt(2))) / (2 * np.tan(1 / np.sqrt(2)))


FINE = 12          # fine-grid oversampling factor for all in-loop integrals


def make_ops(T, m):
    """m control points on [0,T]; all integrals on a FINE-times denser grid
    of the piecewise-linear interpolant (in-loop honesty; the final point is
    re-verified at yet another refinement in verify())."""
    t = np.linspace(0.0, T, m)
    mf = FINE * (m - 1) + 1
    tf = np.linspace(0.0, T, mf)
    dtf = tf[1] - tf[0]
    wf = np.full(mf, dtf); wf[0] = wf[-1] = dtf / 2
    # linear interpolation matrix control -> fine (sparse-ish, dense fine)
    P = np.zeros((mf, m))
    for j, x in enumerate(tf):
        k = min(int(x / (t[1] - t[0])), m - 2)
        lam = (x - t[k]) / (t[1] - t[0])
        P[j, k] = 1 - lam; P[j, k + 1] = lam
    return t, tf, dtf, wf, P


def eval_all(u, tf, dtf, wf):
    """R, J, G, rho(alpha on fine grid) for u given ON THE FINE GRID.
    rho_k = trapezoid_{t in [k dtf, T]} u(t) conj(u(t - k dtf)):
    discrete correlation with exact trapezoid endpoint correction."""
    R = np.abs(np.sum(wf * u)) ** 2
    mf = len(u)
    full = np.correlate(u, u, mode="full")
    # NOTE: np.correlate CONJUGATES its second argument; passing
    # np.conj(u) double-conjugates and corrupts every complex-u
    # autocorrelation (G-W4-10) -- real-u calibration cannot see it
    pos = full[mf - 1:]                                  # lags 0..mf-1
    corr = 0.5 * (u * np.conj(u[0]) + u[-1] * np.conj(u)[::-1])
    rho = np.real(dtf * (pos - corr))
    al = np.arange(mf) * dtf
    band = al <= 1.0 + 1e-12
    J = 2.0 * np.trapezoid(al[band] * rho[band], al[band])
    G = rho[0]
    return R, J, G, rho, al


def optimize(T=1.5, m=61, seed=0, restarts=4, oob_margin=2e-4,
             verbose=True):
    t, tf, dtf, wf, P = make_ops(T, m)
    noob0 = int(np.ceil((1.0 + 1e-9) / dtf)) + 1

    def unpack(z):
        return P @ (z[:m] + 1j * z[m:])

    def negLB(z):
        u = unpack(z)
        R, J, G, rho, al = eval_all(u, tf, dtf, wf)
        return J + G

    def eqR(z):
        u = unpack(z)
        return np.abs(np.sum(wf * u)) ** 2 - 1.0

    def oob(z):
        u = unpack(z)
        _, _, _, rho, al = eval_all(u, tf, dtf, wf)
        return -(rho[noob0:] + oob_margin)

    rng = np.random.default_rng(seed)
    u0c = np.where(t <= 1.0, np.cos(np.sqrt(2) * (t - 0.5)), 0.0)
    u0f = P @ u0c
    u0c = u0c / np.abs(np.sum(wf * u0f))
    best = None
    for k in range(restarts):
        z0 = np.concatenate([u0c, np.zeros(m)])
        if k:
            z0 += 0.10 * rng.standard_normal(2 * m) * np.exp(
                -((np.concatenate([t, t]) - 1.0) ** 2) / 0.1)
        res = minimize(negLB, z0, method="SLSQP",
                       constraints=[dict(type="eq", fun=eqR),
                                    dict(type="ineq", fun=oob)],
                       options=dict(maxiter=500, ftol=1e-12))
        val = 2.0 - res.fun
        ok = (abs(eqR(res.x)) < 1e-8) and (oob(res.x).min() > -1e-8)
        if verbose:
            print(f"   restart {k}: LB = {val:.7f}  feasible = {ok}  "
                  f"({res.message[:44]})")
        if ok and (best is None or val > best[0]):
            best = (val, res.x)
    return best, (t, tf, dtf, wf, P)


def verify(zbest, T, m, refine=4):
    """A-posteriori verification: the SAME piecewise-linear control-point
    function re-evaluated at refine*FINE resolution with the endpoint-exact
    trapezoid correlation of eval_all; reduced costs; rho <= 0 on the dense
    grid with a Lipschitz certificate."""
    t = np.linspace(0.0, T, m)
    dt = t[1] - t[0]
    u = zbest[:m] + 1j * zbest[m:]
    m4 = refine * FINE * (m - 1) + 1
    t4 = np.linspace(0, T, m4)
    u4 = np.interp(t4, t, u.real) + 1j * np.interp(t4, t, u.imag)
    dt4 = t4[1] - t4[0]
    w4 = np.full(m4, dt4); w4[0] = w4[-1] = dt4 / 2
    R, J, G, rho, al = eval_all(u4, t4, dt4, w4)
    LB = min(1 + R, 2 * R) - J - G
    # reduced costs for m = 1..5 at mu_c = min(1+R, 2R)
    mu = min(1 + R, 2 * R)
    rcost = [(1 if mm == 1 else 0) + mm * mm * R - mu * mm
             for mm in range(1, 6)]
    oobmax = rho[al > 1.0].max() if (al > 1.0).any() else -np.inf
    # rho Lipschitz bound: |rho'| <= 2 ||u||_2 ||u'||_2  (pw-linear exact)
    du = np.diff(u) / dt
    lip = 2 * np.sqrt(np.sum(np.abs(u) ** 2) * dt) * \
        np.sqrt(np.sum(np.abs(du) ** 2) * dt)
    print(f"   VERIFY fine({refine}x): R = {R:.9f}  J = {J:.9f}  "
          f"G = {G:.9f}")
    print(f"   VERIFY fine({refine}x): LB = min(1+R,2R)-J-G = {LB:.7f}")
    print(f"   reduced costs m=1..5 (need >= 0): "
          + " ".join(f"{r:+.3e}" for r in rcost))
    print(f"   oob max rho on dense fine grid = {oobmax:+.3e} "
          f"(need <= 0); rho Lipschitz <= {lip:.3f}, grid step {dt4:.5f} "
          f"-> certified oob max <= {oobmax + lip * dt4 / 2:+.3e}")
    # pair-column scope: C_y = int 4 cosh^2(2 pi a y) rho(a) da >= 2 mu?
    print("   pair-column margins C_y - 2*mu_c (>=0 extends the bound to "
          "adversaries with pairs at depth y):")
    for y in (0.05, 0.1, 0.2, 0.3, 0.4, 0.5):
        ch = 4 * np.cosh(2 * np.pi * al * y) ** 2
        Cy = 2 * np.trapezoid(ch * rho, al)   # even: 2 * int_0^T
        print(f"      y = {y:.2f}: {Cy - 2 * mu:+.4f}")
    return LB


if __name__ == "__main__":
    T = float(sys.argv[1]) if len(sys.argv) > 1 else 1.5
    m = int(sys.argv[2]) if len(sys.argv) > 2 else 97
    print("== calibration gate: MT window, band-only ==")
    tg = np.linspace(0.0, 1.0, m)
    u0 = np.cos(np.sqrt(2) * (tg - 0.5))
    mf = 8 * FINE * (m - 1) + 1
    tf = np.linspace(0, 1.0, mf); dtf = tf[1] - tf[0]
    wf = np.full(mf, dtf); wf[0] = wf[-1] = dtf / 2
    uf = np.interp(tf, tg, u0).astype(complex)
    R0, J0, G0, _, _ = eval_all(uf, tf, dtf, wf)
    gate = 2 - (J0 + G0) / R0            # scale-normalized to R = 1
    print(f"   LB(MT) = {gate:.7f}  (target V_A = {VA:.7f}; "
          f"delta = {gate - VA:+.2e})")
    print(f"\n== optimize doubly-positive certificate, T = {T}, m = {m} ==")
    best, ops = optimize(T=T, m=m)
    if best is None:
        print("   NO feasible optimized point -- side stays OPEN")
    else:
        print(f"\n   best raw LB = {best[0]:.7f}")
        verify(best[1], T, m)
