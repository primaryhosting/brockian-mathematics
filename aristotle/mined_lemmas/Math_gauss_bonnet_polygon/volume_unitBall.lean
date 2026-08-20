/-
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Metric Set Module Real
open scoped RealInnerProductSpace ENNReal Pointwise

namespace Math

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The cross product of two vectors of `ℝ³`. -/

theorem volume_unitBall : volume {x : E3 | ‖x‖ < 1} = ENNReal.ofReal (4 * π / 3) := by
  have h : {x : E3 | ‖x‖ < 1} = ball (0 : E3) 1 := by ext x; simp [mem_ball, dist_eq_norm]
  rw [h, EuclideanSpace.volume_ball]
  have hg : Real.Gamma ((3:ℝ)/2 + 1) = 3/4 * √π := by
    rw [Real.Gamma_add_one (by norm_num), show (3:ℝ)/2 = 1/2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  simp only [Fintype.card_fin]
  rw [show ((3:ℕ):ℝ)/2 + 1 = (3:ℝ)/2 + 1 by norm_num, hg]
  have hpi : √π ^ 3 = π * √π := by
    rw [show (3:ℕ) = 2 + 1 by rfl, pow_succ, Real.sq_sqrt Real.pi_pos.le]
  rw [hpi, show π * √π / (3 / 4 * √π) = 4 * π / 3 by
    have : √π ≠ 0 := by positivity
    field_simp]
  simp

