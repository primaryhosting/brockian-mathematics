"""W4 (out-of-band positivity pricing) -- THE FRAME LEMMA + endpoint price.

REGIME LABELS (program law): every claim below is tagged
  [CERT-2LEVEL] = the refereed exact-cone 2-level certificate class C0 (+rungs)
  [DATA-1DELTA] = the one-delta data-regime class (T1 Variant A/B basis)

LEMMA F (OOB vacuity in the 2-level frame) [CERT-2LEVEL, exact algebra]:
  For any (S_O, S_P, X) with S_O >= 0, S_P >= 0 and the exact cone
  X^2 <= 4 S_O S_P (i.e. |X| <= 2 sqrt(S_O S_P)), pointwise in alpha:
      S_total = S_O + S_P + X >= S_O + S_P - 2 sqrt(S_O S_P)
              = (sqrt(S_O) - sqrt(S_P))^2 >= 0.
  Hence the out-of-band rows "S_total(alpha) >= 0, alpha in (1, A]" of the
  ladder class are IMPLIED by the cone: adding out-of-band spectral
  positivity to ANY rung of W3's ladder (C0, C0+I5, ..., the full endpoint)
  changes nothing.  The constraint's entire content in the 2-level class is
  already spent.  Proof is the two displayed inequalities; the numeric block
  below is a spot check only.

CONSEQUENCE (Q2, ordering "endpoint first") [CERT-2LEVEL]:
  value(C0+I5 + OOB) = V_A = 2 - 1/c1* EXACTLY, both sides:
    lower: W3's algebraic I5 dual (algebraic_i5.py) uses only the I5 row,
      the count row and psi >= 0 -- untouched by extra rows.  (Cited, refereed.)
    upper: the refD-style mixture witness rebuilt below (refD's builders were
      lost with the scratchpad; rebuilt from REFEREED.md D1's description):
        x * GUE + (1-x) * ghost-0,   x = V_A,
      GUE   = all-simple, eta_GUE(x) = -sinc^2(pi x),
              S_O = alpha on [0,1], = 1 out of band, S_P = X = 0;
      ghost-0 (refC-refereed) = p_{0.1} = 1/2, tall cell eta = 50 on
              [0, 0.02), psi == 0, X = alpha - S_O - S_P on [0,1],
              X = -2 sqrt(S_O S_P)+ slack out of band (any cone-feasible X).
      EXACT I5 ALGEBRA: mixture I5 LHS = 3x + 4*(1-x)*(1/2) = 2 + x, and
        2 + x >= 4 - 1/c1*  <=>  x >= 2 - 1/c1* = V_A: the witness value
        SATURATES I5 exactly at x = V_A (machine-checked at 30 dps below).
  MARGINAL PRICE of out-of-band positivity on top of the refereed endpoint,
  in the certificate class: 0.  EXACTLY.  Both orderings inside the 2-level
  frame (C0+OOB first: ghost-0 satisfies the cone, hence Lemma F keeps it
  feasible; value stays 0).

  The entire V_A -> V_B increment therefore lives in the ONE-DELTA frame
  [DATA-1DELTA] -- where there is no free cross channel and S(alpha) >= 0
  out of band is a real constraint on the full correlation spectrum.
  Priced in vb_ladder.py.
"""
import numpy as np
import mpmath as mp

mp.mp.dps = 30
c1 = 2 * mp.tan(1 / mp.sqrt(2)) / (mp.sqrt(2) + mp.tan(1 / mp.sqrt(2)))
VA = 2 - 1 / c1
RHS44 = 4 - 1 / c1

print("== constants (30 dps) ==")
print(f"   c1* = {mp.nstr(c1, 20)}")
print(f"   V_A = 2 - 1/c1* = {mp.nstr(VA, 20)}")

# ---------------- Lemma F spot check (proof is the docstring algebra) ------
rng = np.random.default_rng(41)
so = rng.uniform(0, 10, 200_000)
sp = rng.uniform(0, 10, 200_000)
x = rng.uniform(-1, 1, 200_000) * 2 * np.sqrt(so * sp)   # any cone point
st = so + sp + x
print("\n== Lemma F spot check (200k random exact-cone points) ==")
print(f"   min S_total over cone samples = {st.min():.6e}  (lemma: >= 0)")
assert st.min() >= -1e-13

# ---------------- mixture witness, continuum, tol = 0 ----------------------
VAf = float(VA)


def gue(a):
    """(S_O, S_P, X) of the GUE component; band+oob closed form."""
    a = np.asarray(a, float)
    so = np.where(a <= 1.0, a, 1.0)
    return so, np.zeros_like(a), np.zeros_like(a)


def ghost0(a):
    """(S_O, S_P, X) of refC's ghost-0; X band-forced, oob at cone floor."""
    a = np.asarray(a, float)
    asafe = np.where(np.abs(a) < 1e-12, 1.0, a)
    so = np.where(np.abs(a) < 1e-12, 2.0,
                  50.0 * np.sin(2 * np.pi * asafe * 0.02) / (np.pi * asafe))
    sp = 2.0 * np.cosh(0.2 * np.pi * a) ** 2
    x = np.where(a <= 1.0, a - so - sp, -2.0 * np.sqrt(np.maximum(so * sp, 0)))
    return so, sp, x


def check_component(name, f, na=2_000_001, A=25.0, band_eq=True):
    a = np.linspace(0.0, A, na)
    so, sp, x = f(a)
    band = a <= 1.0
    cs = x ** 2 - 4 * so * sp                    # cone residual (<= 0 req.)
    rel = cs / np.maximum(4 * so * sp + x ** 2, 1.0)   # fp-scaled residual
    st = so + sp + x
    r_band = np.max(np.abs(st[band] - a[band])) if band_eq else None
    print(f"   [{name}] min S_O = {so.min():+.3e}  min S_P = {sp.min():+.3e}")
    print(f"   [{name}] max cone residual X^2 - 4 S_O S_P = {cs.max():+.3e}"
          f"  (relative {rel.max():+.3e}; oob X sits ON the cone floor, so"
          f" any positive value at fp-epsilon scale is rounding)")
    print(f"   [{name}] band |S_total - alpha| max = {r_band:.3e}" if band_eq
          else f"   [{name}] (band equality not asserted)")
    print(f"   [{name}] min oob S_total = {st[~band].min():+.3e} (Lemma F: >=0)")
    return so, sp, x, a


print("\n== components on [0, 25] (ghost-0's refereed window reach A <= 25) ==")
check_component("GUE  ", gue)
check_component("ghost", ghost0)

print("\n== mixture x*GUE + (1-x)*ghost-0 at x = V_A, tol = 0 ==")
A = 25.0
a = np.linspace(0.0, A, 2_000_001)
g = gue(a); h = ghost0(a)
so = VAf * g[0] + (1 - VAf) * h[0]
sp = VAf * g[1] + (1 - VAf) * h[1]
x = VAf * g[2] + (1 - VAf) * h[2]
band = a <= 1.0
st = so + sp + x
print(f"   band |S_total - alpha| max = {np.max(np.abs(st[band]-a[band])):.3e}")
print(f"   cone residual max = {np.max(x**2 - 4*so*sp):+.3e}  "
      f"(SOC convexity predicts <= 0)")
print(f"   min oob S_total = {st[~band].min():+.3e}   min S_O = {so.min():+.3e}")
print(f"   eta_GUE >= -1: min of -sinc^2 = -1 at x=0 (exact); "
      f"ghost eta = 50 >= -1 (exact)")
# count + I5, exact at 30 dps
xm = VA
count = xm * 1 + (1 - xm) * (2 * mp.mpf(1) / 2)
i5lhs = 3 * xm + 4 * ((1 - xm) * mp.mpf(1) / 2)
print(f"   count = {mp.nstr(count, 20)}  (= 1 exact: {count == 1})")
print(f"   I5 LHS = 2 + x = {mp.nstr(i5lhs, 20)}")
print(f"   I5 RHS = 4 - 1/c1* = {mp.nstr(RHS44, 20)}")
print(f"   I5 slack = {mp.nstr(i5lhs - RHS44, 5)}  (saturation is EXACT "
      f"algebra: 2 + V_A = 4 - 1/c1* <=> V_A = 2 - 1/c1*)")
assert mp.almosteq(i5lhs, RHS44, abs_eps=mp.mpf(10) ** -28)

print("\nVERDICT [CERT-2LEVEL]: value(C0+I5 + out-of-band S>=0) = V_A exactly,")
print("both sides; marginal price of OOB positivity in the 2-level certificate")
print("class = 0 at every rung (Lemma F).  The V_A -> V_B increment is a")
print("[DATA-1DELTA] phenomenon only.")
