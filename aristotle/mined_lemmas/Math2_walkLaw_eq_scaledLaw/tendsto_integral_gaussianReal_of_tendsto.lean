import RequestProject.CLT

/-!
# Convergence of the rescaled walk against smooth test functions

`Math2.walkLaw μ n t` is the law of `S_{⌊n t⌋} / √n`, where `S` is a random walk with step
distribution `μ`.  Here we prove that, for a centered step distribution with unit variance and
finite third absolute moment, the integrals of smooth test functions against `walkLaw μ n t`
converge to the corresponding integrals against the centered Gaussian law of variance `t`, which
is the law of Brownian motion at time `t`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- The law of `S_p / √n`, the sum of `p` i.i.d. steps with law `μ`, rescaled by `1/√n`. -/

theorem tendsto_integral_gaussianReal_of_tendsto {g : ℝ → ℝ} {M : ℝ} (hg : Continuous g)
    (hgb : ∀ x, |g x| ≤ M) {v : ℕ → ℝ≥0} {w : ℝ≥0} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => ∫ x, g x ∂(gaussianReal 0 (v n))) atTop
      (𝓝 (∫ x, g x ∂(gaussianReal 0 w))) := by
  have key : ∀ u : ℝ≥0, ∫ x, g x ∂(gaussianReal 0 u)
      = ∫ x, g (Real.sqrt u * x) ∂(gaussianReal 0 1) := by
    intro u
    have hsq : (⟨(Real.sqrt u) ^ 2, sq_nonneg _⟩ : ℝ≥0) = u := by
      ext
      simp [Real.sq_sqrt u.coe_nonneg]
    calc ∫ x, g x ∂(gaussianReal 0 u)
        = ∫ x, g x ∂(gaussianReal 0 (⟨(Real.sqrt u) ^ 2, sq_nonneg _⟩ : ℝ≥0)) := by rw [hsq]
      _ = ∫ x, g (Real.sqrt u * x) ∂(gaussianReal 0 1) := by
          rw [gaussianReal_eq_map (Real.sqrt u), integral_map_const_mul _ _ hg]
  simp only [key]
  have hvr : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 (w : ℝ)) := by
    exact (NNReal.tendsto_coe.2 hv)
  refine tendsto_integral_of_dominated_convergence (fun _ => M) ?_ (integrable_const M) ?_ ?_
  · intro n
    exact (hg.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · intro n
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hgb _
  · filter_upwards with x
    have : Tendsto (fun n => Real.sqrt (v n) * x) atTop (𝓝 (Real.sqrt w * x)) :=
      ((Real.continuous_sqrt.tendsto _).comp hvr).mul tendsto_const_nhds
    exact (hg.tendsto _).comp this

