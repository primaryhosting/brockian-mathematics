/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Math2

/-- The linearly interpolated, rescaled random walk
`W_n(t) = (S_{⌊nt⌋} + (nt - ⌊nt⌋) X_{⌊nt⌋}) / √n`, where `S_m = X_0 + ⋯ + X_{m-1}`.
This is the classical Donsker polygonal process associated to the steps `X`. -/

lemma tendsto_integral_gaussianReal {v : ℕ → ℝ≥0} {v₀ : ℝ≥0}
    (h : Tendsto (fun n ↦ (v n : ℝ)) atTop (𝓝 (v₀ : ℝ))) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n ↦ ∫ x, f x ∂(gaussianReal 0 (v n))) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 v₀))) := by
  have key : ∀ w : ℝ≥0,
      ∫ x, f x ∂(gaussianReal 0 w) = ∫ x, f (Real.sqrt w * x) ∂(gaussianReal 0 1) := by
    intro w
    conv_lhs => rw [gaussianReal_eq_map_sqrt w]
    rw [integral_map (by fun_prop) f.continuous.aestronglyMeasurable]
  simp_rw [key]
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ ‖f‖) (fun n ↦ ?_) ?_ ?_ ?_
  · exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact integrable_const _
  · intro n; exact Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm _
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    exact (f.continuous.tendsto _).comp (((Real.continuous_sqrt.tendsto _).comp h).mul_const x)

/-- The partial sums of i.i.d. standard Gaussians are centred Gaussian with variance `m`. -/
