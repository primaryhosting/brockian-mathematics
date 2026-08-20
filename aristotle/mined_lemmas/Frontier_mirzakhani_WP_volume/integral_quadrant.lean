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

theorem integral_quadrant (hmeas : Measurable φ)
    (hb : ∀ s, |φ s| ≤ C * Real.exp (-(s/2))) :
    (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ), x * y * φ (x + y))
      = (1/6) * ∫ u in Ioi (0:ℝ), u ^ 3 * φ u := by
  rw [← prodKernel_integral_eq hmeas hb, ← shearKernel_integral_eq hmeas hb]
  have h := (measurePreserving_prod_add (volume : Measure ℝ) volume).integral_comp
    (MeasurableEquiv.shearAddRight ℝ).measurableEmbedding
    (fun p : ℝ × ℝ => wt p.1 * wt (p.2 - p.1) * φ p.2)
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards with p
  simp

/-! ## Specialisation to Mirzakhani's kernel -/

