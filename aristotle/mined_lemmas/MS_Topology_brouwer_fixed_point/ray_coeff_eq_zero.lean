import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

lemma ray_coeff_eq_zero {x u : E} (hx : ‖x‖ = 1) (ha : 0 < ⟪x, u⟫) :
    ((-⟪x, u⟫ + Real.sqrt (⟪x, u⟫ ^ 2 + ‖u‖ ^ 2 * (1 - ‖x‖ ^ 2))) / ‖u‖ ^ 2) = 0 := by
  have h0 : (1 : ℝ) - ‖x‖ ^ 2 = 0 := by rw [hx]; norm_num
  rw [h0, mul_zero, add_zero, Real.sqrt_sq ha.le, neg_add_cancel, zero_div]

/-- A `C¹` self map of the closed unit ball has a fixed point. -/
