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


lemma rad_mem_cone {F : E → E} {S T : Set E} {v : E} (hv : v ∈ cone S) (hT : T ⊆ sph)
    (hF : F (‖v‖⁻¹ • v) ∈ T) : rad F v ∈ cone T := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv.1
  have hradnorm : ‖rad F v‖ = ‖v‖ := norm_rad hv.1 hT hF
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    rw [h0, norm_zero] at hradnorm
    exact hpos.ne hradnorm
  · rw [hradnorm]; exact hv.2.1
  · rw [hradnorm]
    simp only [rad, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    exact hF

