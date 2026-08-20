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

lemma integrable_prodKernel (hmeas : Measurable φ)
    (hb : ∀ s, |φ s| ≤ C * Real.exp (-(s/2))) :
    Integrable (fun p : ℝ × ℝ => wt p.1 * wt p.2 * φ (p.1 + p.2)) (volume.prod volume) := by
  have hmaj : Integrable
      (fun p : ℝ × ℝ => C *
        ((wt p.1 * Real.exp (-(p.1/2))) * (wt p.2 * Real.exp (-(p.2/2)))))
      (volume.prod volume) :=
    (integrable_wt_exp.mul_prod integrable_wt_exp).const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · exact ((measurable_wt.comp measurable_fst).mul (measurable_wt.comp measurable_snd) |>.mul
      (hmeas.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards with p
    have hsplit : Real.exp (-((p.1 + p.2)/2))
        = Real.exp (-(p.1/2)) * Real.exp (-(p.2/2)) := by
      rw [← Real.exp_add]; ring_nf
    have hw : 0 ≤ wt p.1 * wt p.2 := mul_nonneg (wt_nonneg _) (wt_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    calc wt p.1 * wt p.2 * |φ (p.1 + p.2)|
        ≤ wt p.1 * wt p.2 * (C * Real.exp (-((p.1 + p.2)/2))) :=
          mul_le_mul_of_nonneg_left (hb _) hw
      _ = C * ((wt p.1 * Real.exp (-(p.1/2))) * (wt p.2 * Real.exp (-(p.2/2)))) := by
          rw [hsplit]; ring

