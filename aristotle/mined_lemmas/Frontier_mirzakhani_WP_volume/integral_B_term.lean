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

lemma integral_B_term (a b c : ℝ) :
    (∫ x in Ioi (0:ℝ), x * (mirzKernel x a + mirzKernel x b) * (c + x ^ 2 / 2))
      = c * (F1 a + F1 b) + (F3 a + F3 b) / 2 := by
  have h1a : IntegrableOn (fun x : ℝ => c * (x * mirzKernel x a)) (Ioi 0) := by
    have := (intOn_pow_mirzKernel 1 a).const_mul c
    simpa [pow_one] using this
  have h1b : IntegrableOn (fun x : ℝ => c * (x * mirzKernel x b)) (Ioi 0) := by
    have := (intOn_pow_mirzKernel 1 b).const_mul c
    simpa [pow_one] using this
  have h3a : IntegrableOn (fun x : ℝ => (1/2) * (x ^ 3 * mirzKernel x a)) (Ioi 0) :=
    (intOn_pow_mirzKernel 3 a).const_mul _
  have h3b : IntegrableOn (fun x : ℝ => (1/2) * (x ^ 3 * mirzKernel x b)) (Ioi 0) :=
    (intOn_pow_mirzKernel 3 b).const_mul _
  have h12 : IntegrableOn
      (fun x : ℝ => c * (x * mirzKernel x a) + c * (x * mirzKernel x b)) (Ioi 0) := h1a.add h1b
  have h34 : IntegrableOn
      (fun x : ℝ => (1/2) * (x ^ 3 * mirzKernel x a)
        + (1/2) * (x ^ 3 * mirzKernel x b)) (Ioi 0) := h3a.add h3b
  have hcongr : (∫ x in Ioi (0:ℝ), x * (mirzKernel x a + mirzKernel x b) * (c + x ^ 2 / 2))
      = ∫ x in Ioi (0:ℝ), ((c * (x * mirzKernel x a) + c * (x * mirzKernel x b))
          + ((1/2) * (x ^ 3 * mirzKernel x a) + (1/2) * (x ^ 3 * mirzKernel x b))) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _
    show x * (mirzKernel x a + mirzKernel x b) * (c + x ^ 2 / 2)
      = (c * (x * mirzKernel x a) + c * (x * mirzKernel x b))
        + ((1/2) * (x ^ 3 * mirzKernel x a) + (1/2) * (x ^ 3 * mirzKernel x b))
    ring
  rw [hcongr, integral_add h12 h34, integral_add h1a h1b, integral_add h3a h3b,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hF1a : (∫ x in Ioi (0:ℝ), x * mirzKernel x a) = F1 a := rfl
  have hF1b : (∫ x in Ioi (0:ℝ), x * mirzKernel x b) = F1 b := rfl
  have hF3a : (∫ x in Ioi (0:ℝ), x ^ 3 * mirzKernel x a) = F3 a := rfl
  have hF3b : (∫ x in Ioi (0:ℝ), x ^ 3 * mirzKernel x b) = F3 b := rfl
  rw [hF1a, hF1b, hF3a, hF3b]
  ring

/-! ## Mirzakhani's recursion for `(g,n) = (0,4)` -/

/-- For `j ∈ {1,2,3}`, `rest04 j` lists the two indices of `{1,2,3}` other than `j`. -/
