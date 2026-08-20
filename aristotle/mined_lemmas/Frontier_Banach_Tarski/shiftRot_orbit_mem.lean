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


lemma shiftRot_orbit_mem (n : ℕ) : (shiftRot ^ n) • (0 : E) ∈ Metric.closedBall (0 : E) 1 := by
  set w : E := (shiftRot ^ n) • (0 : E) with hw
  have hdot : w.ofLp ⬝ᵥ w.ofLp = (2 - 2 * Real.cos (n : ℝ)) / 4 := by
    have h0 := shiftRot_orbit_coords n 0
    have h1 := shiftRot_orbit_coords n 1
    have h2 := shiftRot_orbit_coords n 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
    simp only [dotProduct, Fin.sum_univ_three, ← hw] at *
    rw [h0, h1, h2]
    nlinarith [Real.sin_sq_add_cos_sq (n : ℝ)]
  have hle : w.ofLp ⬝ᵥ w.ofLp ≤ 1 := by
    rw [hdot]
    nlinarith [Real.neg_one_le_cos (n : ℝ)]
  rw [mem_closedBall_zero_iff, norm_eq_sqrt_dotProduct]
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_le_sqrt hle

