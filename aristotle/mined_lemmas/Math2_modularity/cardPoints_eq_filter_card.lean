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

lemma cardPoints_eq_filter_card (W : WeierstrassCurve ℤ) (p : ℕ) [NeZero p] :
    cardPoints W p =
      (Finset.univ.filter fun q : ZMod p × ZMod p =>
        q.2 ^ 2 + (W.a₁ : ZMod p) * q.1 * q.2 + (W.a₃ : ZMod p) * q.2
          = q.1 ^ 3 + (W.a₂ : ZMod p) * q.1 ^ 2 + (W.a₄ : ZMod p) * q.1
            + (W.a₆ : ZMod p)).card + 1 := by
  classical
  rw [cardPoints]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro q _
  simpa using equation_map_iff W p q.1 q.2

/-! ## Numerical verification of modularity for `11a1` -/

/-- The trace of Frobenius of `11a1` at a prime `p`, as an explicitly computable quantity. -/
