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

lemma integral_pow_exp_neg (m n : ℕ) :
    (∫ x in Ioi (0:ℝ), x ^ m * Real.exp (-(((n:ℝ)+1) * x)))
      = (m.factorial : ℝ)/((n:ℝ)+1)^(m+1) := by
  have hr : (0:ℝ) < (n:ℝ)+1 := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (m:ℝ)+1) (r := (n:ℝ)+1)
    (by positivity) hr
  rw [show ((m:ℝ)+1-1) = (m:ℝ) by ring] at h
  rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => t ^ (m:ℝ) * Real.exp (-(((n:ℝ)+1) * t))) ?_]
  · rw [h, Real.Gamma_nat_eq_factorial,
      show ((m:ℝ)+1) = ((m+1 : ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [div_pow, one_pow]
    field_simp
  · intro t ht
    show t ^ m * Real.exp (-(((n:ℝ)+1) * t)) = t ^ (m:ℝ) * Real.exp (-(((n:ℝ)+1) * t))
    rw [Real.rpow_natCast]

/-- Expansion of the Fermi–Dirac weight into a geometric series. -/
