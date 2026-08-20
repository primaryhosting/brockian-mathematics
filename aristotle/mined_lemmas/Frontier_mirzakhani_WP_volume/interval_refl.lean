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

lemma interval_refl (k : ℕ) (t : ℝ) :
    (∫ y in (-t)..(0:ℝ), y^k * fd y)
      = (-1)^k * (t^(k+1)/(k+1) - ∫ u in (0:ℝ)..t, u^k * fd u) := by
  have hneg := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := t) (fun y => y^k * fd y)
  rw [neg_zero] at hneg
  rw [← hneg]
  have heq : (∫ u in (0:ℝ)..t, (-u)^k * fd (-u))
      = ∫ u in (0:ℝ)..t, ((-1)^k * u^k - (-1)^k * (u^k * fd u)) := by
    refine intervalIntegral.integral_congr ?_
    intro u hu
    have h : fd (-u) = 1 - fd u := by linarith [fd_add_neg u]
    show (-u)^k * fd (-u) = (-1)^k * u^k - (-1)^k * (u^k * fd u)
    rw [h, neg_pow]
    ring
  rw [heq]
  rw [intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable
        exact continuous_const.mul ((continuous_pow k).mul continuous_fd))]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow]
  simp
  ring

/-- Linearity of the shifted first moment. -/
