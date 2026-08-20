import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_closedBall_E3 : volume (closedBall (0 : E3) 1) = ENNReal.ofReal (4 * π / 3) := by
  rw [EuclideanSpace.volume_closedBall]
  simp only [Fintype.card_fin]
  rw [show ((3:ℕ):ℝ) / 2 + 1 = 1 / 2 + 1 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq,
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hpi : (0:ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have h3 : √π ^ 3 = π * √π := by
    rw [pow_succ, pow_two, Real.mul_self_sqrt Real.pi_pos.le]
  field_simp [h3]
  rw [Real.sq_sqrt Real.pi_pos.le]
  ring

/-- A hyperplane through the origin is null. -/
