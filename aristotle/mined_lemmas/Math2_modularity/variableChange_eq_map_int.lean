/-
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`, so the required
-- header appears above as a block comment and is repeated as a docstring below.)

import Mathlib

/-!
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open CongruenceSubgroup

namespace Math2

/-- The number of points of the reduction mod `p` of an integral Weierstrass curve,
counted on the affine model together with the point at infinity. -/

lemma variableChange_eq_map_int (W : WeierstrassCurve ℚ) [W.IsShortNF] (d : ℕ) (hd0 : (d : ℚ) ≠ 0)
    (A B : ℤ) (hA : (A : ℚ) = (d : ℚ) ^ 4 * W.a₄) (hB : (B : ℚ) = (d : ℚ) ^ 6 * W.a₆) :
    (⟨(Units.mk0 (d : ℚ) hd0)⁻¹, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ℚ) • W
      = (⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℤ).map (Int.castRingHom ℚ) := by
  have ha₁ : W.a₁ = 0 := W.a₁_of_isShortNF
  have ha₂ : W.a₂ = 0 := W.a₂_of_isShortNF
  have ha₃ : W.a₃ = 0 := W.a₃_of_isShortNF
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
      ha₁, ha₂, ha₃] <;>
    simp [hA, hB]

/-- The discriminant of the integral short Weierstrass curve `y² = x³ + Ax + B`. -/
