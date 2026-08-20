import RequestProject.Paradoxical

/-!
# Banach Tarski: a free group of rotations of `ℝ³`
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Set Function

/-! ## A free group of rotations of `ℝ³`

Following the classical argument, the two rotations by `arccos (3/5)` about the `z`- and the
`x`-axis generate a free subgroup of `SO(3)`.  Freeness is proved by a `5`-adic argument:
a nonempty reduced word of length `n`, applied to the integral vector `(1,0,2)` and rescaled
by `5 ^ n`, gives an integral vector which is nonzero modulo `5`.
-/

namespace FreeRotations

open Matrix

/-- The special orthogonal group of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩


lemma rad_rad_apply {F G : E → E} {T : Set E} {v : E} (hv : v ≠ 0) (hT : T ⊆ sph)
    (hF : F (‖v‖⁻¹ • v) ∈ T) (hGF : G (F (‖v‖⁻¹ • v)) = ‖v‖⁻¹ • v) : rad G (rad F v) = v := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hradnorm : ‖rad F v‖ = ‖v‖ := norm_rad hv hT hF
  have h1 : ‖rad F v‖⁻¹ • rad F v = F (‖v‖⁻¹ • v) := by
    rw [hradnorm]
    simp only [rad, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  show ‖rad F v‖ • G (‖rad F v‖⁻¹ • rad F v) = v
  rw [h1, hGF, hradnorm, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

/-- The cone construction turns an equidecomposition of subsets of the sphere into an
equidecomposition of the corresponding cones. -/
