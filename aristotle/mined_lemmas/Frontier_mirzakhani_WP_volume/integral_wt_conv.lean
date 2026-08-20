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

lemma integral_wt_conv (u : ℝ) : (∫ x : ℝ, wt x * wt (u - x)) = wt3 u := by
  rcases lt_or_ge 0 u with hu | hu
  · have hrw : (fun x : ℝ => wt x * wt (u - x))
        = Set.indicator (Ioo (0:ℝ) u) (fun x => x * (u - x)) := by
      funext x
      by_cases hx : 0 < x
      · by_cases hx2 : x < u
        · rw [wt_of_pos hx, wt_of_pos (by linarith), indicator_of_mem (mem_Ioo.mpr ⟨hx, hx2⟩)]
        · rw [wt_of_nonpos (by linarith : u - x ≤ 0), indicator_of_notMem, mul_zero]
          simp only [mem_Ioo, not_and, not_lt]
          intro _; linarith
      · rw [wt_of_nonpos (by linarith : x ≤ 0), indicator_of_notMem, zero_mul]
        simp only [mem_Ioo, not_and, not_lt]
        intro h; exact absurd h hx
    rw [hrw, integral_indicator measurableSet_Ioo, wt3_of_pos hu,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu.le]
    have hcalc : ∫ x in (0:ℝ)..u, x * (u - x) = u ^ 3 / 6 := by
      have h1 : ∫ x in (0:ℝ)..u, x * (u - x) = ∫ x in (0:ℝ)..u, (u * x - x ^ 2) := by
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        ring
      rw [h1, intervalIntegral.integral_sub
        ((intervalIntegral.intervalIntegrable_id).const_mul u)
        (intervalIntegral.intervalIntegrable_pow 2)]
      rw [intervalIntegral.integral_const_mul, integral_id, integral_pow]
      norm_num
      ring
    rw [hcalc]
  · have hrw : (fun x : ℝ => wt x * wt (u - x)) = fun _ => 0 := by
      funext x
      by_cases hx : 0 < x
      · rw [wt_of_nonpos (by linarith : u - x ≤ 0), mul_zero]
      · rw [wt_of_nonpos (by linarith : x ≤ 0), zero_mul]
    rw [hrw, integral_zero, wt3_of_nonpos hu]

