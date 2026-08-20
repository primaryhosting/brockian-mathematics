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


lemma cone_sph_eq : cone sph = Metric.closedBall (0 : E) 1 \ {0} := by
  ext v
  constructor
  · rintro ⟨hv0, hv1, -⟩
    exact ⟨by simpa using hv1, hv0⟩
  · rintro ⟨hv1, hv0⟩
    have hv0' : v ≠ 0 := hv0
    have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv0'
    refine ⟨hv0', by simpa using hv1, ?_⟩
    rw [mem_sph_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos),
      inv_mul_cancel₀ hpos.ne']

/-- **The punctured closed unit ball is paradoxical**, using rotations only. -/
