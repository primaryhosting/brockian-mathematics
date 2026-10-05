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

lemma equation_map_iff (W : WeierstrassCurve ℤ) (p : ℕ) (x y : ZMod p) :
    (W.map (Int.castRingHom (ZMod p))).toAffine.Equation x y ↔
      y ^ 2 + (W.a₁ : ZMod p) * x * y + (W.a₃ : ZMod p) * y
        = x ^ 3 + (W.a₂ : ZMod p) * x ^ 2 + (W.a₄ : ZMod p) * x + (W.a₆ : ZMod p) := by
  rw [WeierstrassCurve.Affine.equation_iff']
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, Int.coe_castRingHom, WeierstrassCurve.toAffine,
    Int.cast_id]
  constructor <;> intro h <;> linear_combination h

/-- The point count as an explicit, decidable `Finset` cardinality. -/
