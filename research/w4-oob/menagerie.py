"""W4 Q3: the witness menagerie vs out-of-band spectral positivity.

For each witness in the program's menagerie, three verdicts:
  [2LV-OOB]  does it satisfy S_total >= 0 out of band in the 2-LEVEL frame?
             (Lemma F: automatic for every exact-cone point -> the
             constraint kills NOTHING in the certificate class)
  [1D-EXIST] does the witness exist in the one-delta frame at all
             (band equality without the free cross channel)?
  [1D-OOB]   if it exists there, does S(alpha) >= 0 out of band?

Computed here: the Variant-A optimal adversary's oob spectrum (the one
object that S >= 0 actually kills); everything else cites the committed
verifications (frame_lemma.py, controls.py, ghosts.py/W3-refereed).
"""
import numpy as np
import oned

print("== the one genuine kill: T1 Variant-A optimal adversary ==")
r = oned.solve(label="Variant A optimum", XF=80.0, na=601, tol=2e-4,
               dual=False)
x, meta = r["x"], r["meta"]
lo, hi = meta["lo"], meta["hi"]
iE, iT, ntail = meta["iE"], meta["iT"], meta["ntail"]
eta = x[iE:iT]; tails = x[iT:]
ao = np.linspace(1.0 + 1e-6, 5.0, 8001)
S = np.empty_like(ao)
for i, a in enumerate(ao):
    S[i] = (np.arange(1, 6) ** 2 @ x[:5]
            + oned.t1.cell_cols(a, lo, hi) @ eta
            + oned.t1.tail_cols(a, 80.0) @ (tails[:ntail] - tails[ntail:]))
imin = int(np.argmin(S))
print(f"   S(alpha) on (1, 5]: min = {S[imin]:+.4f} at alpha = "
      f"{ao[imin]:.4f}; S < 0 on {100 * np.mean(S < 0):.1f}% of the grid")
print(f"   -> the Variant-A extremal configuration VIOLATES out-of-band"
      f" positivity massively [1D-OOB: DIES]")
print(f"   (Referee A's R1 missing-constraint attack, reproduced from"
      f" this program's own committed solve)")

print("""
== MENAGERIE TABLE (verdicts + provenance) ==
witness                     2LV-OOB          1D-EXIST          1D-OOB
---------------------------------------------------------------------------
GUE (all-simple)            PASS (Lemma F)   YES (closed form) PASS: S=1 oob
                            [frame_lemma]    [controls C2]     (structural)
ghost-0 (refC, psi==0)      PASS (Lemma F +  NO: S(0+)=4 != 0  -- (does not
  p_.1=1/2 + tall cell      direct check,    without the X     exist there)
                            frame_lemma)     channel
ghost-2 (W3 multiplicity    PASS (its S =    NO: S(0+)=2 != 0  -- (does not
  ghost, psi_2=1/4)         1+cosh^2 > 0     without X         exist there)
                            everywhere)
refD mixture                PASS (verified   NO (ghost-0       --
  V_A*GUE+(1-V_A)*ghost-0   tol=0, incl. I5  component)
                            saturation)
sec.7.5(a) all-pairs        PASS (= ghost-0  INFEASIBLE at     never reached:
                            up to depth      band-only: Fejer  dead before
                            bookkeeping)     cap D2+4p<=4/3,   S>=0 is asked
                                             t* = 0.81 [C3]
T1 Variant-A extremal       n/a (1-delta     YES (it is the    DIES (above:
  (simples+doubles+CCLM17   object)          band-only         S << 0 on
  correlation)                               optimum)          most of oob)
deep-pair increment         PASS             YES (depth-       SURVIVES and
  (rescaled, R3 exponent                     capped class)     HELPS: pairs
  law)                                                         inject e^{4piAy}
                                                               POSITIVE oob mass;
                                                               active at the
                                                               depth cap w/ mass
                                                               6e-5 [log_pairs]
W4 crystallized adversary   n/a              YES (Variant-B    SURVIVES: S
  (eta = -1 + integer-                       optimum)          touches 0 on
  spaced peaks, psi_2~0.158)                                   thick oob sets
                                                               [log_anatomy]
---------------------------------------------------------------------------
STRUCTURE OF THE SURVIVING FAMILY: out-of-band positivity is a
FRAME-DEPENDENT killer.  In the 2-level certificate class it kills nothing
(cone-implied, Lemma F) -- every ghost survives untouched, so the ladder's
certified constants are unchanged.  In the one-delta data frame it kills
exactly one thing: the smooth CCLM17-type extremal correlation (whose oob
spectrum is very negative).  What survives is (a) GUE and its mixtures,
(b) configurations whose correlation CRYSTALLIZES (hard anticorrelation
eta = -1 + near-integer-spaced positive peaks, spectrum pinned to 0 on
out-of-band intervals -- the binding adversary of the doubly-positive
problem), and (c) vanishing-mass deep pairs at the class depth cap, which
BUY oob positivity (their spectral injection is positive) at o(1) band
cost -- the R3 exponent law re-entering on the adversary's side.
""")
