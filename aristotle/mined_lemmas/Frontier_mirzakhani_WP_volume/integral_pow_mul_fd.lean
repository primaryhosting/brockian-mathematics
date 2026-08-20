import Mathlib
import RequestProject.Kernel
import RequestProject.TwoDim

/-!
# Weil–Petersson volume polynomials in low complexity

We record the Weil–Petersson volume polynomials `V_{0,3}`, `V_{0,4}` and `V_{0,5}`, the
right-hand sides of Mirzakhani's recursion in the cases `(g,n) = (0,4)` and `(0,5)`, and
verify the recursion in both cases, together with the fact that the recursion determines
the volume polynomial.
-/

open scoped BigOperators Real
open MeasureTheory Set Real

namespace Frontier

set_option maxHeartbeats 1000000

/-! ## The volume polynomials -/

/-- `V_{0,3} ≡ 1`: the moduli space of pairs of pants is a point. -/

lemma integral_pow_mul_fd (m : ℕ) :
    (∫ x in Ioi (0:ℝ), x^m * fd x) = 2^(m+1) * ∫ x in Ioi (0:ℝ), x^m / (1 + Real.exp x) := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi
    (fun y : ℝ => y^m / (1 + Real.exp y)) 0 (b := 1/2) (by norm_num)
  simp only [mul_zero, smul_eq_mul] at h
  have hlhs : (∫ x in Ioi (0:ℝ), (1/2 * x)^m / (1 + Real.exp (1/2 * x)))
      = (1/2)^m * ∫ x in Ioi (0:ℝ), x^m * fd x := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    show (1/2 * x)^m / (1 + Real.exp (1/2 * x)) = (1/2)^m * (x^m * fd x)
    have hp : (0:ℝ) < 1 + Real.exp (1/2 * x) := by positivity
    have hfdx : fd x = 1 / (1 + Real.exp (1/2 * x)) := by
      unfold fd; rw [show x / 2 = 1/2 * x by ring]
    rw [hfdx, mul_pow]
    field_simp
  rw [hlhs] at h
  have hpow : (2:ℝ)^m * (1/2)^m = 1 := by rw [← mul_pow]; norm_num
  calc (∫ x in Ioi (0:ℝ), x^m * fd x)
      = 2^m * ((1/2)^m * ∫ x in Ioi (0:ℝ), x^m * fd x) := by rw [← mul_assoc, hpow, one_mul]
    _ = 2^m * (2 * ∫ x in Ioi (0:ℝ), x^m / (1 + Real.exp x)) := by rw [h]; norm_num
    _ = 2^(m+1) * ∫ x in Ioi (0:ℝ), x^m / (1 + Real.exp x) := by rw [pow_succ]; ring

/-- The first moment `∫₀^∞ x · fd x dx = π²/3`. -/
