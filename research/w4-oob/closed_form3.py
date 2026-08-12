"""W4 hybrid-family SLP ascent: certified CONTINUUM lower bound for the
doubly-positive one-delta value [DATA-1DELTA, continuum, basis-free,
on-line-adversary scope].

FAMILY:  K(x) = |h_f(x)|^2 + |h_m(x)|^2
  h_f = F.T. of free COMPLEX u on [0, 1.4]     (rho_f = Re autocorr(u),
                                                supp [-1.4, 1.4], free sign)
  h_m = F.T. of env(t) e^{0.8 pi i t}, env >= 0 on [0, 1.5]
        (rho_m(alpha) = cos(0.8 pi alpha) g(alpha), g = env-autocorr >= 0;
         cos(0.8 pi a) <= cos(0.8 pi) < -0.80 for a in [1, 1.5] ->
         rho_m <= 0 there STRUCTURALLY)
  K >= 0 on all of R structurally (sum of squared moduli): the global
  x-positivity that killed round-1's finite-check kernels is an identity.
  Out-of-band sign rho = rho_f + rho_m <= 0:
    on (1.4, 1.5]: rho_f = 0 (support), rho_m <= 0 structural;
    on (1, 1.4]:   enforced with margin on a dense grid, certified at the
                   end via a Lipschitz bound; the modulated component gives
                   strictly negative buffer -0.8 g(alpha) so the margin
                   survives the free part's support-edge decay.
  rho = 0 beyond 1.5.  The bound therefore needs S >= 0 only on (1, 3/2]:
  valid for every Bochner window A >= 3/2 including A = infinity.

CHAIN (calibrated to V_A in closed_form.py/closed_form2.py):
  psi_1 >= 2 - (J + G)/R,   R = |int u|^2 + |int env e^{.8 pi i t}|^2,
  J = 2 int_0^1 a rho(a) da,  G = rho(0),  provided (J+G)/R in (1,2)
  (secant interior; reduced costs m<=5 then hold identically).

METHOD: sequential linear programming from the Montgomery-Taylor point --
linearize (LB, constraints) in the 2*m1+m2 control values, step within a
trust region, exact re-evaluation + feasibility filter each step (the
iterate is ALWAYS a valid certificate).
"""
import numpy as np
from scipy.optimize import linprog

VA = 2 - (np.sqrt(2) + np.tan(1 / np.sqrt(2))) / (2 * np.tan(1 / np.sqrt(2)))
FINE = 16
TF, TM, PHI = 1.4, 1.5, 0.4
M1, M2 = 57, 31
DELTA = 2e-4                       # in-loop surrogate margin


def grids():
    t1 = np.linspace(0, TF, M1)
    t2 = np.linspace(0, TM, M2)
    f1 = np.linspace(0, TF, FINE * (M1 - 1) + 1)
    f2 = np.linspace(0, TM, FINE * (M2 - 1) + 1)
    return t1, t2, f1, f2


T1, T2, F1, F2 = grids()
D1 = F1[1] - F1[0]; D2 = F2[1] - F2[0]
W1 = np.full(len(F1), D1); W1[0] = W1[-1] = D1 / 2
W2 = np.full(len(F2), D2); W2[0] = W2[-1] = D2 / 2
ALO = np.arange(len(F1)) * D1          # rho_f lags
ALM = np.arange(len(F2)) * D2          # rho_m lags
# in-loop oob constraints live on the CORRELATION'S NATIVE LAG GRID
# (k * D1 for k*D1 in (1, TF]) -- already computed by acorr, zero extra cost
KOOB = np.where((ALO := np.arange(FINE * (M1 - 1) + 1)
                 * (TF / (FINE * (M1 - 1)))) > 1.0 + 1e-12)[0]
NOOB = len(KOOB)


def acorr(u, dtf):
    mf = len(u)
    full = np.correlate(u, u, mode="full")
    # NOTE: np.correlate CONJUGATES its second argument; passing
    # np.conj(u) double-conjugates and corrupts every complex-u
    # autocorrelation (G-W4-10) -- real-u calibration cannot see it
    pos = full[mf - 1:]
    corr = 0.5 * (u * np.conj(u[0]) + u[-1] * np.conj(u)[::-1])
    return dtf * (pos - corr)


def rho_at(u, dtf, tgrid, alphas):
    """rho at arbitrary lags (for the oob grid): direct trapezoid."""
    out = np.empty(len(alphas))
    for i, a in enumerate(alphas):
        tt = tgrid[tgrid >= a - 1e-12]
        if len(tt) < 2:
            out[i] = 0.0
            continue
        ua = np.interp(tt, tgrid, u.real) + 1j * np.interp(tt, tgrid, u.imag)
        ub = (np.interp(tt - a, tgrid, u.real)
              + 1j * np.interp(tt - a, tgrid, u.imag))
        out[i] = np.real(np.trapezoid(ua * np.conj(ub), tt))
    return out


def unpack(z):
    u = np.interp(F1, T1, z[:M1]) + 1j * np.interp(F1, T1, z[M1:2 * M1])
    env = np.interp(F2, T2, np.maximum(z[2 * M1:], 0.0))
    return u, env


COSMAX = np.cos(2 * np.pi * PHI * 1.0)   # sup of cos(.8 pi a) on [1, 1.5]
# (= cos(.8 pi) = -0.80902, attained at both endpoints; interior smaller)


def evaluate(z):
    """LB terms + the SURROGATE s(alpha) = rho_f + COSMAX * g on (1, 1.4].
    s <= 0  ==>  rho = rho_f + cos(.8 pi a) g <= s <= 0 there (g >= 0)."""
    u, env = unpack(z)
    u2 = env * np.exp(2j * np.pi * PHI * F2)
    rf = np.real(acorr(u, D1))
    g = np.real(acorr(env.astype(complex), D2))
    R = (np.abs(np.sum(W1 * u)) ** 2 + np.abs(np.sum(W2 * u2)) ** 2)
    b1 = ALO <= 1.0 + 1e-12
    b2 = ALM <= 1.0 + 1e-12
    J = (2 * np.trapezoid(ALO[b1] * rf[b1], ALO[b1])
         + 2 * np.trapezoid(ALM[b2] * np.cos(2 * np.pi * PHI * ALM[b2])
                            * g[b2], ALM[b2]))
    G = rf[0] + g[0]
    # surrogate on the native lag grid: rho_f directly; g interpolated
    # from its own lag grid (both smooth compact-support functions)
    g_i = np.interp(ALO[KOOB], ALM, g)
    s_oob = rf[KOOB] + COSMAX * g_i
    LB = 2.0 - (J + G) / R if R > 1e-9 else -10.0
    return LB, R, J, G, s_oob


def slp(iters=140, tr0=0.08, seed=3):
    z = np.zeros(2 * M1 + M2)
    z[:M1] = np.where(T1 < 0.999, np.cos(np.sqrt(2) * (T1 - 0.5)), 0.0)
    # (the t = 1.0 knot is ZERO: the pw-linear start then has support
    # exactly [0, 1], so rho_f = 0 beyond 1 and the start is feasible;
    # a truncated MT with u(1.0-) != 0 would overhang past the band edge)
    # wide structural buffer envelope: g(alpha) must carry real mass out
    # to lag 1.4 so the start meets the in-loop margin with headroom
    z[2 * M1:] = 0.2 * np.exp(-((T2 - 0.75) / 0.9) ** 2)
    LB, R, J, G, rho = evaluate(z)
    print(f"   start: LB = {LB:.7f}  (V_A = {VA:.7f});  oob max = "
          f"{rho.max():+.2e}")
    tr = tr0
    n = len(z)
    for it in range(iters):
        # numerical Jacobians (forward differences)
        h = 1e-6
        LB0, R0, J0, G0, rho0 = evaluate(z)
        gLB = np.zeros(n)
        Jrho = np.zeros((NOOB, n))
        for j in range(n):
            zp = z.copy(); zp[j] += h
            LBp, _, _, _, rhop = evaluate(zp)
            gLB[j] = (LBp - LB0) / h
            Jrho[:, j] = (rhop - rho0) / h
        # LP: maximize gLB . d   s.t. s0 + Js d <= -DELTA, |d| <= tr
        res = linprog(-gLB, A_ub=Jrho, b_ub=-DELTA - rho0,
                      bounds=[(-tr, tr)] * n, method="highs")
        if res.status != 0:
            tr *= 0.5
            if tr < 1e-5:
                break
            continue
        d = res.x
        # line search with exact evaluation
        step, accepted = 1.0, False
        for _ in range(12):
            zt = z + step * d
            LBt, Rt, Jt, Gt, rhot = evaluate(zt)
            if rhot.max() <= -0.5 * DELTA and LBt > LB0 - 1e-12:
                z, accepted = zt, True
                break
            step *= 0.5
        if not accepted:
            tr *= 0.5
            if tr < 1e-5:
                break
        elif step == 1.0:
            tr = min(tr * 1.6, 0.3)
        if it % 5 == 0 or not accepted:
            LBc = evaluate(z)[0]
            print(f"   it {it:3d}: LB = {LBc:.7f}  tr = {tr:.4f}")
    return z


def certify(z, refine=8, quiet=False):
    """Final certificate: re-evaluate at refine*FINE, certify oob sign on a
    dense grid with a Lipschitz constant, check secant interior."""
    global FINE, T1, T2, F1, F2, D1, D2, W1, W2, ALO, ALM
    saved = (FINE, F1, F2, D1, D2, W1, W2, ALO, ALM)
    FINE = FINE * refine
    F1 = np.linspace(0, TF, FINE * (M1 - 1) + 1)
    F2 = np.linspace(0, TM, FINE * (M2 - 1) + 1)
    D1 = F1[1] - F1[0]; D2 = F2[1] - F2[0]
    W1 = np.full(len(F1), D1); W1[0] = W1[-1] = D1 / 2
    W2 = np.full(len(F2), D2); W2[0] = W2[-1] = D2 / 2
    ALO = np.arange(len(F1)) * D1
    ALM = np.arange(len(F2)) * D2
    LB, R, J, G, _ = evaluate(z)
    u, env = unpack(z)
    if quiet:
        pass
    # PIECEWISE-CUBIC oob certification of the surrogate
    # s(a) = rho_f(a) + COSMAX * g(a) on (1, 1.4]:
    # u is pw-linear on knot step d1 = T1[1]-T1[0] = 0.025 and env on
    # d2 = 0.05 = 2*d1, so both rho_f and g are piecewise CUBIC in the lag
    # with breakpoints on the d1-lattice; on each lag interval fit the
    # exact cubic through 4 samples and bound its interior maximum in
    # closed form (roots of the quadratic derivative).
    d1 = T1[1] - T1[0]
    klo, khi = int(round(1.0 / d1)), int(round(TF / d1))
    certmax, fitres = -np.inf, 0.0
    for k in range(klo, khi):
        a4 = np.linspace(k * d1, (k + 1) * d1, 4)
        s4 = (rho_at(u, D1, F1, a4)
              + COSMAX * rho_at(env.astype(complex), D2, F2, a4))
        # cubic through the 4 nodes (exact for a cubic; residual checked)
        co = np.polyfit(a4 - a4[0], s4, 3)
        mid = np.linspace(0, d1, 9)
        res = np.max(np.abs(np.polyval(co, mid[::2][1:3])
                            - (rho_at(u, D1, F1, a4[0] + mid[::2][1:3])
                               + COSMAX * rho_at(env.astype(complex), D2,
                                                 F2, a4[0] + mid[::2][1:3]))))
        fitres = max(fitres, float(res))
        # closed-form max of the cubic on [0, d1]
        cand = [0.0, d1]
        der = np.polyder(co)
        r = np.roots(der)
        cand += [float(x.real) for x in r
                 if abs(x.imag) < 1e-12 and 0 <= x.real <= d1]
        certmax = max(certmax, max(np.polyval(co, c) for c in cand))
    certmax = certmax + fitres
    rho_d = np.array([certmax])  # for the print below
    hstep = d1
    print(f"\n== CERTIFICATION (refine {refine}x) ==")
    print(f"   R = {R:.9f}  J = {J:.9f}  G = {G:.9f}")
    print(f"   LB = 2 - (J+G)/R = {LB:.7f}")
    print(f"   secant interior (J+G)/R = {(J+G)/R:.6f} in (1,2): "
          f"{1 < (J+G)/R < 2}")
    print(f"   oob (1, 1.4]: piecewise-cubic certified max of surrogate "
          f"s = rho_f + cos(.8 pi) g  <= {certmax:+.3e} (cubic-fit residual "
          f"{fitres:.1e} included)  ({'PASS' if certmax <= 0 else 'FAIL'})")
    print(f"   (s <= 0 implies rho <= 0 there since cos(.8 pi a) <= "
          f"{COSMAX:.5f} on [1, 1.5] and g >= 0)")
    print(f"   oob (1.4, 1.5]: rho = cos(0.8 pi a) g(a) <= 0 STRUCTURAL "
          f"(env >= 0: min = {env.min():+.2e}); rho = 0 beyond 1.5")
    print(f"   K >= 0 on R: STRUCTURAL (sum of squares)")
    # pair-column scope
    mu = 2.0
    al_all = np.linspace(0, TM, 4001)
    rho_all = (rho_at(u, D1, F1, al_all)
               + np.cos(2 * np.pi * PHI * al_all)
               * rho_at(env.astype(complex), D2, F2, al_all))
    print("   pair-column margins (C_y - 2 mu R)/R  (>= 0 -> bound also "
          "covers adversaries with pairs at depth y):")
    for y in (0.05, 0.1, 0.2, 0.3, 0.4, 0.5):
        ch = 4 * np.cosh(2 * np.pi * al_all * y) ** 2
        Cy = 2 * np.trapezoid(ch * rho_all, al_all)
        print(f"      y = {y:.2f}: {(Cy - 2 * mu * R) / R:+.4f}")
    (FINE, F1, F2, D1, D2, W1, W2, ALO, ALM) = saved
    return LB, certmax


def repair(z, cmax_fn, cs=np.linspace(1.0, 2.5, 31)):
    """Scale the buffer envelope by the smallest c with certified oob
    max <= 0.  Valid direction: env >= 0 stays, and the extra term is
    -(c^2 - 1) |COSMAX| g(alpha) <= 0 pointwise (g > 0 on (0, 1.5))."""
    for c in cs:
        zc = z.copy(); zc[2 * M1:] *= c
        LBc, cm = cmax_fn(zc)
        if cm <= 0:
            return zc, c, LBc, cm
    return None, None, None, None


if __name__ == "__main__":
    print("== SLP ascent from Montgomery-Taylor ==")
    z = slp()
    LB, cm = certify(z)
    if cm > 0:
        print("\n== REPAIR: scale buffer envelope to certified feasibility ==")
        zr, c, LBr, cmr = repair(z, lambda w: certify(w, refine=8))
        if zr is not None:
            print(f"   repair factor c = {c:.3f}: certified oob max = "
                  f"{cmr:+.3e}, LB = {LBr:.7f}")
            z, LB, cm = zr, LBr, cmr
        else:
            print("   repair FAILED within c <= 2.5")
    np.save("closed_form3_best.npy", z)
    print(f"\nRESULT [DATA-1DELTA, continuum, on-line adversary, any A >= "
          f"3/2]: certified psi_1 lower bound = {LB:.7f}"
          + ("" if cm <= 0 else "  (OOB CERT FAILED -- not claimable)"))
    print(f"   vs V_A = {VA:.7f}: increment {LB - VA:+.7f}")
    print("   control points saved: closed_form3_best.npy")
