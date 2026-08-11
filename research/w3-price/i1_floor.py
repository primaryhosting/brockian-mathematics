"""W3: continuum lower-bound certificate for level C0+I1 (coherence at 0).

CHAIN (every constant machine-checked below; valid for ANY correlation
measure nu >= 0, any tails, any Bochner window -- no grid, no cells):

 (1) PAIR-KILLING AT 0.  Band row at alpha = 0 (tol form):
     S_O(0) + S_P(0) + X(0) <= tol, with S_O(0) >= 0, X(0) >= 0 (I1 row),
     S_P(0) = 4 sum_y p_y  ==>  sum_y p_y <= tol/4.
     Justification of I1 for genuine configurations: at alpha = 0 every
     on-line x off-line cross term is 2 w cos(0) cosh(0) = 2w >= 0, so
     the genuine cross channel has X(0) >= 0.  [First unjustified step of
     this level: none on the constraint itself; the residual assumption is
     the CLASS's own band/delta_0 bookkeeping, refereed in W2/refC.]

 (2) MONTGOMERY-TAYLOR WINDOW DUAL (with explicit pair remainder).
     k := |vhat|^2 >= 0 everywhere (a square), v(s) = cos(sqrt2 s) 1_{|s|<=1/2},
     khat = v * v >= 0, supp khat in [-1,1].  Pair the positive measure
     sigma_O = D2 delta_0 + nu (nu >= 0) with k:
        k(0) D2  <=  int k dsigma_O  =  khat(0) + int khat(a) S_O(a) da.
     Young on the exact cone (any eps in (0,1)): X >= -(eps S_O + S_P/eps),
     so the band equality gives  S_O <= [a + (1/eps - 1) S_P]/(1 - eps),
     and S_P(a) <= 4 cosh(pi)^2 (tol/4) =: Cp tol on [0,1] (worst depth .5).
     Hence, normalising k(0) = 1:
        D2 <= khat(0) + [ int |a| khat da + (1/eps - 1) Cp tol int khat ] / (1-eps).
     At tol = 0, eps -> 0:  D2 <= khat(0) + int |a| khat = 1/c1*  (MT).

 (3) SPECIES ALGEBRA.  With S := sum m psi_m = 1 - 2 sum p >= 1 - tol/2 and
     D2 = sum m^2 psi_m <= M*:   psi_1 >= 2 S - M*  (doubles are the worst
     deviation: psi_1 >= S - (M* - S)/(m-1), minimised at m = 2).

 FLOOR(tol) = 2 (1 - tol/2) - min_eps [ khat(0) + (int|a|khat + (1/eps-1) Cp
              tol int khat)/(1-eps) ];   FLOOR(0) = 2 - 1/c1* = 0.6725007.
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 30
c1 = 2 * mp.tan(1 / mp.sqrt(2)) / (mp.sqrt(2) + mp.tan(1 / mp.sqrt(2)))


def v(s):
    return mp.cos(mp.sqrt(2) * s) if abs(s) <= mp.mpf(1) / 2 else mp.mpf(0)


def khat(a):        # (v*v)(a) = int v(s) v(s-a) ds, supp [-1,1]
    a = abs(a)
    if a >= 1:
        return mp.mpf(0)
    return mp.quad(lambda s: v(s) * v(s - a), [a - mp.mpf(1) / 2, mp.mpf(1) / 2])


def k0():           # k(0) = (int v)^2  (k = |vhat|^2, vhat(0) = int v)
    return mp.quad(v, [-mp.mpf(1) / 2, mp.mpf(1) / 2]) ** 2


print("== MT window constants (30 dps, my own quadrature) ==")
K0 = k0()
Kh0 = khat(0)
Iabs = 2 * mp.quad(lambda a: a * khat(a), [0, 1])
Iall = 2 * mp.quad(khat, [0, 1]) + 0  # int_{-1}^{1} khat
print(f"   k(0) = {mp.nstr(K0, 12)}   khat(0) = {mp.nstr(Kh0, 12)}")
print(f"   int |a| khat = {mp.nstr(Iabs, 12)}   int khat = {mp.nstr(Iall, 12)}")
ratio = (Kh0 + Iabs) / K0
print(f"   (khat(0) + int|a|khat)/k(0) = {mp.nstr(ratio, 12)}")
print(f"   1/c1*                       = {mp.nstr(1 / c1, 12)}   "
      f"(match: {mp.nstr(abs(ratio - 1 / c1), 3)})")
assert abs(ratio - 1 / c1) < mp.mpf("1e-12")

print("\n== k >= 0 and khat >= 0 (structural, not finite-check) ==")
print("   k = |vhat|^2 is a modulus square -> k >= 0 on all of R (exact).")
print("   khat = v*v with v >= 0 on its support (cos(sqrt2 s) > 0 for "
      "|s| <= 1/2 since sqrt2/2 < pi/2) -> khat >= 0 (exact).")

Cp = 4 * mp.cosh(mp.pi) ** 2 / 4      # S_P <= 4 cosh(pi)^2 sum p; sum p <= tol/4
print(f"\n== FLOOR(tol) with pair remainder, Cp = cosh(pi)^2 = {mp.nstr(4*Cp/4,8)} ==")
for tol in (mp.mpf(0), mp.mpf("2e-4"), mp.mpf("1e-5")):
    best = -mp.inf
    for eps in [mp.mpf(x) / 1000 for x in range(1, 400, 2)]:
        Mstar = (Kh0 + (Iabs + (1 / eps - 1) * Cp * tol * Iall) / (1 - eps)) / K0
        fl = 2 * (1 - tol / 2) - Mstar
        if fl > best:
            best, beps = fl, eps
    print(f"   tol = {mp.nstr(tol, 3):>8}:  FLOOR = {mp.nstr(best, 10)}"
          f"   (eps* = {mp.nstr(beps, 3)})")
print(f"\n   FLOOR(0) = 2 - 1/c1* = {mp.nstr(2 - 1/c1, 12)}  EXACT.")
print("   => C0+I1 certified constant >= 0.6725007 at tol = 0 (continuum,")
print("      any nu, any window); at the shipped tol = 2e-4 the continuum")
print("      floor printed above applies; the grid dual (ladder.py L1A)")
print("      certifies the grid value independently.")
