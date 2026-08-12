"""W4 final structural-family ascent (v4).  Supersedes closed_form3's SLP:
v3's two failure modes (R -> 0 scale pole; constraint-grid threading by
lag-aliased oscillation, G-W4-9) are both closed STRUCTURALLY here:
  * normalization R = 1 is restored by exact rescaling z /= sqrt(R) after
    every accepted step (all terms quadratic) -- no pole exists;
  * the oob constraints ARE the certified quantities: s = rho_f +
    cos(.8 pi) g restricted to each lag interval [k d1, (k+1) d1] is an
    exact CUBIC (pw-linear controls on uniform knots), and the SLP
    constrains the per-interval closed-form cubic MAXIMA m_k(z) <= -delta.
    There is no grid between the constraint and the certificate.
Family, chain, calibration: as closed_form3.py (docstring there).
"""
import numpy as np
from scipy.optimize import linprog

VA = 2 - (np.sqrt(2) + np.tan(1 / np.sqrt(2))) / (2 * np.tan(1 / np.sqrt(2)))
TF, TM, PHI = 1.4, 1.5, 0.4
M1, M2 = 57, 31
FINE = 16
DELTA = 2e-3
COSMAX = np.cos(2 * np.pi * PHI)          # -0.80902, sup on [1, 1.5]

T1 = np.linspace(0, TF, M1); d1 = T1[1] - T1[0]
T2 = np.linspace(0, TM, M2); d2 = T2[1] - T2[0]
F1 = np.linspace(0, TF, FINE * (M1 - 1) + 1)
F2 = np.linspace(0, TM, FINE * (M2 - 1) + 1)
D1 = F1[1] - F1[0]; D2 = F2[1] - F2[0]
W1 = np.full(len(F1), D1); W1[0] = W1[-1] = D1 / 2
W2 = np.full(len(F2), D2); W2[0] = W2[-1] = D2 / 2
AL1 = np.arange(len(F1)) * D1
AL2 = np.arange(len(F2)) * D2
KLO, KHI = int(round(1.0 / d1)), int(round(TF / d1))   # oob intervals
A4 = np.concatenate([np.linspace(k * d1, (k + 1) * d1, 4)
                     for k in range(KLO, KHI)])         # 4 nodes/interval


def acorr(u, dtf):
    mf = len(u)
    full = np.correlate(u, u, mode="full")
    # NOTE: np.correlate CONJUGATES its second argument; passing
    # np.conj(u) double-conjugates and corrupts every complex-u
    # autocorrelation (G-W4-10) -- real-u calibration cannot see it
    pos = full[mf - 1:]
    corr = 0.5 * (u * np.conj(u[0]) + u[-1] * np.conj(u)[::-1])
    return dtf * (pos - corr)


def rho_at(uR, uI, tgrid, alphas):
    out = np.empty(len(alphas))
    for i, a in enumerate(alphas):
        tt = tgrid[tgrid >= a - 1e-12]
        if len(tt) < 2:
            out[i] = 0.0; continue
        ua = np.interp(tt, tgrid, uR) + 1j * np.interp(tt, tgrid, uI)
        ub = (np.interp(tt - a, tgrid, uR)
              + 1j * np.interp(tt - a, tgrid, uI))
        out[i] = np.real(np.trapezoid(ua * np.conj(ub), tt))
    return out


def cubic_maxima(svals):
    """svals: s at the 4 uniform nodes of each interval; returns per-
    interval EXACT max of the interpolating cubic (s IS that cubic)."""
    out = []
    for k in range(len(svals) // 4):
        y = svals[4 * k:4 * k + 4]
        co = np.polyfit(np.linspace(0, d1, 4), y, 3)
        cand = [0.0, d1]
        r = np.roots(np.polyder(co))
        cand += [float(x.real) for x in r
                 if abs(x.imag) < 1e-12 and 0 < x.real < d1]
        out.append(max(np.polyval(co, c) for c in cand))
    return np.array(out)


def evaluate(z):
    uR = np.interp(F1, T1, z[:M1]); uI = np.interp(F1, T1, z[M1:2 * M1])
    u = uR + 1j * uI
    env = np.interp(F2, T2, np.maximum(z[2 * M1:], 0.0))
    u2 = env * np.exp(2j * np.pi * PHI * F2)
    rf = np.real(acorr(u, D1))
    g = np.real(acorr(env.astype(complex), D2))
    R = (np.abs(np.sum(W1 * u)) ** 2 + np.abs(np.sum(W2 * u2)) ** 2)
    b1 = AL1 <= 1.0 + 1e-12
    b2 = AL2 <= 1.0 + 1e-12
    J = (2 * np.trapezoid(AL1[b1] * rf[b1], AL1[b1])
         + 2 * np.trapezoid(AL2[b2] * np.cos(2 * np.pi * PHI * AL2[b2])
                            * g[b2], AL2[b2]))
    G = rf[0] + g[0]
    s4 = (rho_at(uR, uI, F1, A4)
          + COSMAX * rho_at(env, np.zeros(len(F2)), F2, A4))
    mk = cubic_maxima(s4)
    return R, J, G, mk


def rescale(z):
    R = evaluate(z)[0]
    return z / np.sqrt(R)


def slp(iters=160, tr0=0.06):
    z = np.zeros(2 * M1 + M2)
    z[:M1] = np.where(T1 < 0.999, np.cos(np.sqrt(2) * (T1 - 0.5)), 0.0)
    z[2 * M1:] = 0.2 * np.exp(-((T2 - 0.75) / 0.9) ** 2)
    z = rescale(z)
    R, J, G, mk = evaluate(z)
    print(f"   start: LB = {2 - (J+G)/R:.7f} (V_A = {VA:.7f}); "
          f"max cubic-max = {mk.max():+.2e}; R = {R:.6f}")
    n, tr = len(z), tr0
    for it in range(iters):
        R0, J0, G0, mk0 = evaluate(z)
        f0 = J0 + G0
        h = 1e-6
        gf = np.zeros(n); gR = np.zeros(n)
        Jm = np.zeros((len(mk0), n))
        for j in range(n):
            zp = z.copy(); zp[j] += h
            Rp, Jp, Gp, mkp = evaluate(zp)
            gf[j] = (Jp + Gp - f0) / h
            gR[j] = (Rp - R0) / h
            Jm[:, j] = (mkp - mk0) / h
        # LP: minimize gf.d  s.t. mk0 + Jm d <= -DELTA, R linearized = 1,
        # |d| <= tr
        res = linprog(gf, A_ub=Jm, b_ub=-DELTA - mk0,
                      A_eq=gR[None, :], b_eq=[1.0 - R0],
                      bounds=[(-tr, tr)] * n, method="highs")
        if res.status != 0:
            tr *= 0.5
            if tr < 1e-5:
                break
            continue
        d = res.x
        step, acc = 1.0, False
        for _ in range(14):
            zt = rescale(z + step * d)
            Rt, Jt, Gt, mkt = evaluate(zt)
            ok = (mkt.max() <= -0.5 * DELTA
                  and Jt + Gt >= Rt - 1e-9          # validity identity
                  and Jt + Gt < f0 / R0 * Rt - 1e-12)
            if ok:
                z, acc = zt, True
                break
            step *= 0.5
        if not acc:
            tr *= 0.5
            if tr < 1e-5:
                break
        elif step == 1.0:
            tr = min(tr * 1.5, 0.25)
        if it % 10 == 0 or not acc:
            R0, J0, G0, mk0 = evaluate(z)
            print(f"   it {it:3d}: LB = {2 - (J0+G0)/R0:.7f}  "
                  f"tr = {tr:.4f}  maxcub = {mk0.max():+.1e}")
    return z


def final_certify(z):
    """High-resolution re-evaluation + cubic re-certification with the
    residual guard, exactly as closed_form3.certify but on this family."""
    global FINE, F1, F2, D1, D2, W1, W2, AL1, AL2
    FINE_s, F1s, F2s, D1s, D2s, W1s, W2s, A1s, A2s = \
        FINE, F1, F2, D1, D2, W1, W2, AL1, AL2
    FINE = 128
    F1 = np.linspace(0, TF, FINE * (M1 - 1) + 1)
    F2 = np.linspace(0, TM, FINE * (M2 - 1) + 1)
    D1 = F1[1] - F1[0]; D2 = F2[1] - F2[0]
    W1 = np.full(len(F1), D1); W1[0] = W1[-1] = D1 / 2
    W2 = np.full(len(F2), D2); W2[0] = W2[-1] = D2 / 2
    AL1 = np.arange(len(F1)) * D1
    AL2 = np.arange(len(F2)) * D2
    R, J, G, mk = evaluate(z)
    # cubic-fit residual guard: re-evaluate s at 2 extra points/interval
    uRf = np.interp(F1, T1, z[:M1]); uIf = np.interp(F1, T1, z[M1:2 * M1])
    envf = np.interp(F2, T2, np.maximum(z[2 * M1:], 0.0))
    z0f = np.zeros(len(F2))
    probe = np.concatenate([np.linspace(k * d1, (k + 1) * d1, 7)[1::2]
                            for k in range(KLO, KHI)])
    sp = (rho_at(uRf, uIf, F1, probe)
          + COSMAX * rho_at(envf, z0f, F2, probe))
    s4 = (rho_at(uRf, uIf, F1, A4)
          + COSMAX * rho_at(envf, z0f, F2, A4))
    res = 0.0
    for k in range(KHI - KLO):
        co = np.polyfit(np.linspace(0, d1, 4), s4[4 * k:4 * k + 4], 3)
        pr = probe[3 * k:3 * k + 3] - (KLO + k) * d1
        res = max(res, float(np.max(np.abs(np.polyval(co, pr)
                                           - sp[3 * k:3 * k + 3]))))
    certmax = mk.max() + res
    LB = 2 - (J + G) / R
    print(f"\n== FINAL CERTIFICATION (FINE = 128) ==")
    print(f"   R = {R:.9f}  J = {J:.9f}  G = {G:.9f}")
    print(f"   LB = 2 - (J+G)/R = {LB:.7f}")
    print(f"   secant interior (J+G)/R in (1,2): {1 < (J+G)/R < 2}")
    print(f"   validity identity J+G >= R: {J + G >= R}")
    print(f"   oob (1,1.4]: certified cubic max + residual = "
          f"{certmax:+.3e}  ({'PASS' if certmax <= 0 else 'FAIL'})")
    print(f"   oob (1.4, 1.5]: structural (env >= 0); 0 beyond 1.5; "
          f"K >= 0 structural")
    mu = 2.0
    alz = np.linspace(0, TM, 3001)
    rr = (rho_at(uRf, uIf, F1, alz)
          + np.cos(2 * np.pi * PHI * alz)
          * rho_at(envf, z0f, F2, alz))
    print("   pair-column margins (C_y - 2 mu R)/R:")
    for y in (0.1, 0.3, 0.5):
        Cy = 2 * np.trapezoid(4 * np.cosh(2 * np.pi * alz * y) ** 2 * rr,
                              alz)
        print(f"      y = {y:.1f}: {(Cy - 2 * mu * R) / R:+.4f}")
    FINE, F1, F2, D1, D2, W1, W2, AL1, AL2 = \
        FINE_s, F1s, F2s, D1s, D2s, W1s, W2s, A1s, A2s
    return LB, certmax


if __name__ == "__main__":
    print("== v4 SLP (cubic-max constraints, pinned scale) ==")
    z = slp()
    LB, cm = final_certify(z)
    np.save("closed_form4_best.npy", z)
    ok = cm <= 0
    print(f"\nRESULT [DATA-1DELTA, continuum, on-line adversary, any "
          f"A >= 3/2]: certified psi_1 >= {LB:.7f}"
          + ("" if ok else "  (NOT CLAIMABLE: oob cert failed)"))
    print(f"   vs V_A = {VA:.7f}: increment {LB - VA:+.7f}")
    if LB > 0.6843:
        print("   WARNING: exceeds the grid-class value 0.6843 -> "
              "self-refuting, do not claim")
