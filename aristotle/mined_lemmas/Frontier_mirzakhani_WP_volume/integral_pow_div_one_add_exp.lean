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

lemma integral_pow_div_one_add_exp (m : ℕ) {S : ℝ}
    (hS : HasSum (fun n : ℕ => (-1:ℝ)^n / ((n:ℝ)+1)^(m+1)) S) :
    (∫ x in Ioi (0:ℝ), x^m / (1 + Real.exp x)) = (m.factorial : ℝ) * S := by
  set F : ℕ → ℝ → ℝ := fun n x => (-1:ℝ)^n * (x^m * Real.exp (-(((n:ℝ)+1) * x))) with hF
  have hF_int : ∀ n, Integrable (F n) (volume.restrict (Ioi (0:ℝ))) := fun n =>
    (intOn_pow_exp_neg m n).const_mul _
  have hnorm : ∀ n, (∫ x in Ioi (0:ℝ), ‖F n x‖) = (m.factorial : ℝ)/((n:ℝ)+1)^(m+1) := by
    intro n
    rw [← integral_pow_exp_neg m n]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    show ‖(-1:ℝ)^n * (x^m * Real.exp (-(((n:ℝ)+1) * x)))‖
        = x^m * Real.exp (-(((n:ℝ)+1) * x))
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_pos hx0, abs_of_pos (Real.exp_pos _)]
  have habs : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^(m+1)) := by
    have h := hS.summable.abs
    refine h.congr (fun n => ?_)
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos (by positivity : (0:ℝ) < ((n:ℝ)+1)^(m+1))]
  have hsummable : Summable (fun n : ℕ => ∫ x in Ioi (0:ℝ), ‖F n x‖) := by
    refine Summable.congr (habs.mul_left (m.factorial : ℝ)) (fun n => ?_)
    rw [hnorm n]; ring
  have hmain := integral_tsum_of_summable_integral_norm hF_int hsummable
  have hlhs : ∑' n, (∫ x in Ioi (0:ℝ), F n x) = (m.factorial : ℝ) * S := by
    have hterm : ∀ n : ℕ, (∫ x in Ioi (0:ℝ), F n x)
        = (m.factorial : ℝ) * ((-1:ℝ)^n / ((n:ℝ)+1)^(m+1)) := by
      intro n
      rw [hF]
      simp only
      rw [integral_const_mul, integral_pow_exp_neg m n]
      ring
    rw [tsum_congr hterm]
    exact (hS.mul_left (m.factorial : ℝ)).tsum_eq
  rw [hlhs] at hmain
  rw [hmain]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  exact ((hasSum_fermi_pow m hx).tsum_eq).symm

