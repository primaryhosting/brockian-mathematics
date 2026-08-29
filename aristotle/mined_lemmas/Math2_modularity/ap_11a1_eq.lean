/-
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalises the statement of the modularity theorem (Taniyama–Shimura–Wiles)
for elliptic curves over `ℚ`, given by integral Weierstrass models, together with a
fully kernel-checked numerical verification of the modularity prediction for the
elliptic curve `11a1 : y² + y = x³ - x² - 10x - 20`, whose associated newform is the
eta product `η(z)² η(11z)²`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Math2

open WeierstrassCurve CongruenceSubgroup MatrixGroups ModularFormClass UpperHalfPlane

/-! ## Point counts of the reductions of a Weierstrass model -/

/-- The number of points of the reduction mod `p` of an integral Weierstrass model `W`:
the affine solutions of the Weierstrass equation over `ℤ/p`, plus the point at infinity.
(For `p = 0` this is junk, and it is only used for primes of good reduction.) -/

lemma ap_11a1_eq (p : ℕ) [NeZero p] :
    ap W11a1 p = (p : ℤ) + 1 -
      ((Finset.univ.filter fun q : ZMod p × ZMod p =>
        q.2 ^ 2 + q.2 = q.1 ^ 3 + (-1 : ZMod p) * q.1 ^ 2 + (-10 : ZMod p) * q.1
          + (-20 : ZMod p)).card + 1) := by
  rw [ap, cardPoints_eq_filter_card]
  norm_num [W11a1]

end Math2

section Test
open Math2
example : newform11Coeff 13 = ap W11a1 13 := by
  rw [ap_11a1_eq]
  decide
end Test

