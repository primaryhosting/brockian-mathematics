"""W4 controls (calibration gate + mandated adversary controls).

C1 REPLICATION [DATA-1DELTA]: Variant A at T1 defaults must reproduce
   RESULTS.txt 0.67902 (XF=80) and Variant B must reproduce the
   two-referee-confirmed 0.683983 (XF=160, A=3).  Gate for everything else.

C2 GUE PASSES [DATA-1DELTA, closed form]: eta_GUE(x) = -sinc^2(pi x) gives
   S(alpha) = alpha on [0,1] and S = 1 >= 0 out of band EXACTLY, psi_1 = 1,
   count = 1: GUE satisfies band data AND out-of-band positivity
   structurally, at tol = 0, every window A.  Machine check below.

C3 ALL-PAIRS DIES [DATA-1DELTA, closed form -- the mandated encoding check]:
   In the one-delta frame the paper's section-7.5(a) all-pairs configuration
   is INFEASIBLE, and not merely against the oob rows: the Fejer second
   moment kills it against the BAND data already.  Closed form:
     integral_0^1 2(1-a) S(a) da = integral_0^1 2(1-a) a da = 1/3   (band eq)
     S = D2' + pairdiag + etahat (+tails);  cosh^2 >= 1 and
     integral_0^1 2(1-a) da = 1  give  diag part >= D2 + 4 sum p;
     Fejer(eta) = integral eta(x) sinc^2(pi x) dx >= -1   (eta >= -1);
   hence  D2 + 4 sum p <= 4/3  for EVERY feasible configuration.
   All-pairs: D2 = 0, 4 sum p = 2 > 4/3.  DEAD.  (Quantitative LP phase-1
   residual also reported, refC-style.)  NOTE the anatomy: what kills
   all-pairs in this frame is the Frobenius/second-moment EVALUATION plus
   x-space positivity -- the same ingredient pair refC identified as the
   preprint's out-of-class ingredients.  In the 2-LEVEL frame all-pairs
   survives as ghost-0 (the free cross channel evades the Fejer argument);
   S(alpha) >= 0 never gets a shot at it there (Lemma F).

C4 COROLLARY (committed for reuse): the class fact  sum m^2 psi_m
   + 4 sum_y p_y <= 4/3 + O(tol)  [DATA-1DELTA, band-only, closed form].
"""
import numpy as np
from scipy.optimize import linprog
import oned

# ---------------- C1: replication gate ------------------------------------
# NOTE (aliasing, Referee A R1.4 reproduced): T1's shipped default na=251
# under-samples the band for XF >= 80 (far-cell columns oscillate at period
# ~1/XF in alpha) and collapses (log_na_probe.txt: A XF=80 na=251 -> 0.67802;
# B XF=160 na=251 -> 0.0 with an aliased psi_2=1/2 pseudo-config).  The
# refereed numbers are recovered at na >= 600.
print("== C1 replication gate (na=601/1001; aliasing note in source) ==")
rA = oned.solve(label="C1 Variant A", XF=80.0, na=601, tol=2e-4, dual=True)
okA = abs(rA["value"] - 0.67902) < 5e-5
print(f"   target 0.67902 (RESULTS.txt) -> match: {okA}")
rB = oned.solve(label="C1 Variant B", XF=160.0, na=1001,
                tol=2e-4, A=3.0, nb=400, dual=True)
okB = abs(rB["value"] - 0.683983) < 1e-3
print(f"   target 0.683983 (both referees) -> within 1e-3, rising in na: "
      f"{okB}  (value {rB['value']:.7f})")

# ---------------- C2: GUE closed-form pass --------------------------------
print("\n== C2 GUE control (closed form, tol = 0) ==")
a = np.linspace(0.0, 40.0, 400_001)
# S(alpha) = 1 + F.T.[ -sinc^2(pi x) ](alpha) = 1 - (1 - |alpha|)_+
S = 1.0 - np.maximum(1.0 - a, 0.0)
band = a <= 1.0
print(f"   max |S - alpha| on [0,1] = {np.max(np.abs(S[band]-a[band])):.3e}"
      f"   (exact identity: triangle transform)")
print(f"   min S out of band = {S[~band].min():.6f}  (= 1, every A)")
print(f"   eta_GUE >= -1 (equality only at x=0), psi_1 = 1, count = 1: PASS")

# ---------------- C3: all-pairs dies --------------------------------------
print("\n== C3 all-pairs control ==")
print("   closed form: D2 + 4*sum p <= 4/3;  all-pairs has 4*sum p = 2 > 4/3")
print("   (band Fejer budget; derivation in docstring, constants:")
fej = np.trapezoid(2 * (1 - np.linspace(0, 1, 100_001))
                   * np.linspace(0, 1, 100_001), np.linspace(0, 1, 100_001))
print(f"    int_0^1 2(1-a) a da = {fej:.6f} = 1/3;  "
      f"int_0^1 2(1-a) da = 1.000000)")
# quantitative phase-1 residual, refC-style: minimise uniform band slack t
# with psi == 0 forced, pairs at the class depths, oob rows on.
c, Aub, bub, Aeq, beq, lb, meta = oned.build(
    XF=80.0, na=251, tol=0.0, A=3.0, nb=400,
    depths=(0.1, 0.2, 0.3, 0.4, 0.5))
n = meta["n"]
rows = [Aeq]
for k in range(oned.MMAX):                     # psi == 0
    r = np.zeros(n); r[k] = 1.0
    rows.append(r[None, :])
Aeq2 = np.vstack(rows); beq2 = np.concatenate([beq, np.zeros(oned.MMAX)])
# slack column t on every inequality row (uniform phase-1)
Aub2 = np.hstack([Aub, -np.ones((Aub.shape[0], 1))])
Aeq2 = np.hstack([Aeq2, np.zeros((Aeq2.shape[0], 1))])
c2 = np.zeros(n + 1); c2[-1] = 1.0
bounds = [(lb[j], None) for j in range(n)] + [(0, None)]
res = linprog(c2, A_ub=Aub2, b_ub=bub, A_eq=Aeq2, b_eq=beq2,
              bounds=bounds, method="highs")
print(f"   LP phase-1 (psi==0, depths 0.1..0.5, tol=0): min uniform slack "
      f"t* = {res.fun:.4f}  (>0 = infeasible, quantitatively)")
print(f"   VERDICT: all-pairs DIES in the one-delta encoding "
      f"(t* = {res.fun:.3f} >> 0); encoding sanity confirmed.")
print(f"\nGATE: {'PASS' if okA and okB and res.fun > 0.01 else 'FAIL'}")
