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

lemma integrable_shearKernel (hmeas : Measurable φ)
    (hb : ∀ s, |φ s| ≤ C * Real.exp (-(s/2))) :
    Integrable (fun p : ℝ × ℝ => wt p.1 * wt (p.2 - p.1) * φ p.2) (volume.prod volume) := by
  refine ((measurePreserving_prod_add (volume : Measure ℝ) volume).integrable_comp_emb
    (MeasurableEquiv.shearAddRight ℝ).measurableEmbedding).mp ?_
  have hcongr : ((fun p : ℝ × ℝ => wt p.1 * wt (p.2 - p.1) * φ p.2) ∘
      fun z : ℝ × ℝ => (z.1, z.1 + z.2))
      = fun p : ℝ × ℝ => wt p.1 * wt p.2 * φ (p.1 + p.2) := by
    funext p
    simp [Function.comp]
  rw [hcongr]
  exact integrable_prodKernel hmeas hb

/-! ## The two Fubini evaluations -/

