"""W4 STRUCTURAL closed-form certificate family for the doubly-positive
one-delta value [DATA-1DELTA, continuum, basis-free].  Supersedes the
general-complex search of closed_form.py (graveyard G-W4-2: SLSQP on the
free family exploits constraint-grid slack / cannot start feasible).

FAMILY (all feasibility conditions are IDENTITIES -- nothing to sign-check):
  K(x) = |h1(x)|^2 + |h2(x)|^2,
    h1 = F.T. of a free COMPLEX u1 on [0, 1]          (spectrum in [-1, 1]),
    h2 = F.T. of env * e^{i pi t}, env >= 0 on [0, 3/2]  (modulated window).
  Then, with g = env * env-autocorrelation (g >= 0 pointwise since env >= 0,
  supp g = [-3/2, 3/2]) and rho1 = Re autocorr(u1) (supp [-1, 1]):
    K >= 0 on R                    STRUCTURAL (sum of squared moduli);
    rho(alpha) = rho1 + cos(pi alpha) g(alpha);
    rho(alpha) <= 0 on (1, 3/2]    STRUCTURAL (rho1 = 0 there; cos(pi a) <= 0
                                   on [1/2, 3/2]; g >= 0);
    rho = 0 beyond 3/2             (supp g).
  Chain (same as closed_form.py, on-line adversary, m <= 5, S >= 0 needed
  only on (1, 3/2] -- valid for every Bochner window A >= 3/2):
    psi_1 >= min(1 + R, 2R) - (J + G)   -> at optimal scale 2 - (J+G)/R,
    R = |int u1|^2 + |int u2|^2,
    J = 2 int_0^1 a [rho1(a) + cos(pi a) g(a)] da,
    G = int |u1|^2 + int env^2.
  Reduced costs r_m = delta_{m1} + m^2 R - mu_c m (m <= 5) and the pair
  columns C_y are checked a posteriori (pair scope reported, not assumed).

The optimizer only IMPROVES a certificate that is valid at every iterate;
env = 0 reproduces the Montgomery-Taylor bound V_A exactly (calibration).
"""
import sys
import numpy as np
from scipy.optimize import minimize

VA = 2 - (np.sqrt(2) + np.tan(1 / np.sqrt(2))) / (2 * np.tan(1 / np.sqrt(2)))
FINE = 10
T2 = 1.5


def fine_ops(m, T):
    t = np.linspace(0.0, T, m)
    mf = FINE * (m - 1) + 1
    tf = np.linspace(0.0, T, mf)
    dtf = tf[1] - tf[0]
    wf = np.full(mf, dtf); wf[0] = wf[-1] = dtf / 2
    return t, tf, dtf, wf


def acorr(u, dtf):
    """trapezoid autocorrelation of fine-grid u at lags k*dtf (complex)."""
    mf = len(u)
    full = np.correlate(u, u, mode="full")
    # NOTE: np.correlate CONJUGATES its second argument; passing
    # np.conj(u) double-conjugates and corrupts every complex-u
    # autocorrelation (G-W4-10) -- real-u calibration cannot see it
    pos = full[mf - 1:]
    corr = 0.5 * (u * np.conj(u[0]) + u[-1] * np.conj(u)[::-1])
    return dtf * (pos - corr)


class Family:
    def __init__(self, m1=41, m2=49):
        self.m1, self.m2 = m1, m2
        self.t1, self.tf1, self.dtf1, self.wf1 = fine_ops(m1, 1.0)
        self.t2, self.tf2, self.dtf2, self.wf2 = fine_ops(m2, T2)

    def unpack(self, z):
        m1, m2 = self.m1, self.m2
        u1c = z[:m1] + 1j * z[m1:2 * m1]
        env = z[2 * m1:2 * m1 + m2]
        return u1c, env

    def terms(self, z):
        u1c, env = self.unpack(z)
        u1 = (np.interp(self.tf1, self.t1, u1c.real)
              + 1j * np.interp(self.tf1, self.t1, u1c.imag))
        e2 = np.interp(self.tf2, self.t2, env)
        u2 = e2 * np.exp(1j * np.pi * self.tf2)
        rho1 = np.real(acorr(u1, self.dtf1))
        g2 = np.real(acorr(e2.astype(complex), self.dtf2))
        al1 = np.arange(len(rho1)) * self.dtf1
        al2 = np.arange(len(g2)) * self.dtf2
        R = (np.abs(np.sum(self.wf1 * u1)) ** 2
             + np.abs(np.sum(self.wf2 * u2)) ** 2)
        b2 = al2 <= 1.0 + 1e-12
        J = (2.0 * np.trapezoid(al1 * rho1, al1)
             + 2.0 * np.trapezoid(al2[b2] * np.cos(np.pi * al2[b2])
                                  * g2[b2], al2[b2]))
        G = rho1[0] + g2[0]
        return R, J, G, (rho1, al1, g2, al2)

    def negLB(self, z):
        R, J, G, _ = self.terms(z)
        if R <= 1e-12:
            return 10.0
        return -(2.0 - (J + G) / R)


def optimize(m1=41, m2=49, restarts=5, seed=1):
    fam = Family(m1, m2)
    rng = np.random.default_rng(seed)
    u0 = np.cos(np.sqrt(2) * (fam.t1 - 0.5))
    best = None
    for k in range(restarts):
        z0 = np.concatenate([u0, np.zeros(m1), np.zeros(m2)])
        if k == 1:      # seed a small envelope bump near the band edge
            z0[2 * m1:] = 0.3 * np.exp(-((fam.t2 - 0.75) / 0.3) ** 2)
        elif k > 1:
            z0[:2 * m1] += 0.1 * rng.standard_normal(2 * m1)
            z0[2 * m1:] = np.abs(0.3 * rng.standard_normal(m2))
        bounds = ([(None, None)] * (2 * m1) + [(0.0, None)] * m2)
        res = minimize(fam.negLB, z0, method="L-BFGS-B", bounds=bounds,
                       options=dict(maxiter=3000, maxfun=300_000,
                                    ftol=1e-14, gtol=1e-10))
        val = -res.fun
        print(f"   restart {k}: LB = {val:.7f}   ({res.message})")
        if best is None or val > best[0]:
            best = (val, res.x.copy())
    return best, fam


def verify(z, fam, refine=6):
    """Re-evaluate the winning control-point functions at refine*FINE
    resolution; check secant interior, reduced costs, pair columns."""
    global FINE
    old = FINE
    FINE = refine * FINE
    fam2 = Family(fam.m1, fam.m2)
    R, J, G, (rho1, al1, g2, al2) = fam2.terms(z)
    FINE = old
    LB = min(1 + R, 2 * R) - (J + G)
    LBn = 2.0 - (J + G) / R          # scale-normalized (the claim)
    mu = 2.0                          # at R -> 1 normalization
    print(f"   VERIFY {refine}x: R = {R:.9f}  J = {J:.9f}  G = {G:.9f}")
    print(f"   VERIFY {refine}x: LB (scale-opt) = 2 - (J+G)/R = {LBn:.7f}")
    JGn = (J + G) / R
    print(f"   secant interior check: (J+G)/R = {JGn:.6f} in (1, 2): "
          f"{1.0 < JGn < 2.0}")
    rc = [(1 if mm == 1 else 0) + mm * mm - 2.0 * mm for mm in range(1, 6)]
    print(f"   reduced costs m=1..5 at R=1, mu_c=2: "
          + " ".join(f"{r:+.1f}" for r in rc) + "  (>= 0 all: "
          f"{all(r >= 0 for r in rc)})")
    # pair columns at R = 1 normalization: C_y/R - 2 mu >= 0 ?
    print("   pair-column margins (C_y - 2 mu_c)/R, oob part included:")
    for y in (0.05, 0.1, 0.2, 0.3, 0.4, 0.5):
        ch1 = 4 * np.cosh(2 * np.pi * al1 * y) ** 2
        ch2 = 4 * np.cosh(2 * np.pi * al2 * y) ** 2
        Cy = (2 * np.trapezoid(ch1 * rho1, al1)
              + 2 * np.trapezoid(ch2 * np.cos(np.pi * al2) * g2, al2))
        print(f"      y = {y:.2f}: {(Cy - 2 * mu * R) / R:+.4f}")
    print(f"   oob structural: rho = cos(pi a) g(a) <= 0 on (1, 1.5] "
          f"IDENTITY (env >= 0 verified: min env = "
          f"{fam.unpack(z)[1].min():+.2e}); rho = 0 beyond 1.5.")
    return LBn


if __name__ == "__main__":
    m1 = int(sys.argv[1]) if len(sys.argv) > 1 else 41
    m2 = int(sys.argv[2]) if len(sys.argv) > 2 else 49
    print("== calibration: env = 0 must give V_A ==")
    fam = Family(m1, m2)
    z0 = np.concatenate([np.cos(np.sqrt(2) * (fam.t1 - 0.5)),
                         np.zeros(m1), np.zeros(m2)])
    print(f"   LB(MT, env=0) = {-fam.negLB(z0):.7f}  (V_A = {VA:.7f})")
    print(f"\n== optimize structural family (m1={m1}, m2={m2}) ==")
    best, fam = optimize(m1, m2)
    print(f"\n   best in-loop LB = {best[0]:.7f}")
    verify(best[1], fam)
    np.save("closed_form2_best.npy", best[1])
    print("   winning control points saved: closed_form2_best.npy")
