import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

lemma det_id_add_smul_ne_zero (A : E →L[ℝ] E) {t : ℝ} (h : ‖t • A‖ < 1) :
    (ContinuousLinearMap.id ℝ E + t • A).det ≠ 0 := by
  rw [ContinuousLinearMap.det, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_ne_iff,
    LinearMap.ker_eq_bot']
  intro y hy
  by_contra hy0
  have h1 : y + (t • A) y = 0 := by simpa using hy
  have h3 : (t • A) y = -y := by linear_combination (norm := module) h1
  have h2 : ‖y‖ ≤ ‖t • A‖ * ‖y‖ := by
    calc ‖y‖ = ‖(t • A) y‖ := by rw [h3, norm_neg]
    _ ≤ ‖t • A‖ * ‖y‖ := (t • A).le_opNorm y
  have := norm_pos_iff.mpr hy0
  nlinarith

