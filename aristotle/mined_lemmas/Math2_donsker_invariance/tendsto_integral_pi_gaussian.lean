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

lemma tendsto_integral_pi_gaussian {k : ℕ} {v : ℕ → Fin k → ℝ≥0} {w : Fin k → ℝ≥0}
    (h : ∀ j, Tendsto (fun n ↦ ((v n j : ℝ≥0) : ℝ)) atTop (𝓝 ((w j : ℝ≥0) : ℝ)))
    (f : BoundedContinuousFunction (Fin k → ℝ) ℝ) :
    Tendsto (fun n ↦ ∫ x, f x ∂(Measure.pi fun j ↦ gaussianReal 0 (v n j))) atTop
      (𝓝 (∫ x, f x ∂(Measure.pi fun j ↦ gaussianReal 0 (w j)))) := by
  have hcont : ∀ z : Fin k → ℝ≥0,
      Continuous fun (x : Fin k → ℝ) (j : Fin k) ↦ Real.sqrt (z j) * x j := by
    intro z; fun_prop
  have key : ∀ z : Fin k → ℝ≥0, ∫ x, f x ∂(Measure.pi fun j ↦ gaussianReal 0 (z j))
      = ∫ x, f (fun j ↦ Real.sqrt (z j) * x j) ∂(Measure.pi fun _ : Fin k ↦ gaussianReal 0 1) := by
    intro z
    rw [pi_gaussianReal_eq_map_sqrt z,
      integral_map (hcont z).measurable.aemeasurable f.continuous.aestronglyMeasurable]
  simp_rw [key]
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ ‖f‖) (fun n ↦ ?_) ?_ ?_ ?_
  · exact (f.continuous.comp (hcont (v n))).aestronglyMeasurable
  · exact integrable_const _
  · intro n; exact Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm _
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    refine (f.continuous.tendsto _).comp (tendsto_pi_nhds.2 fun j ↦ ?_)
    exact ((Real.continuous_sqrt.tendsto _).comp (h j)).mul_const (x j)

section Fdd

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A sum of i.i.d. standard Gaussians over a finite index set is centred Gaussian with variance
the cardinality of the index set. -/
