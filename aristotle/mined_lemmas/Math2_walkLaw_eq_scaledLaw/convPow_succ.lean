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

theorem convPow_succ (μ : Measure ℝ) (n : ℕ) : convPow μ (n + 1) = (convPow μ n) ∗ μ := rfl

instance isProbabilityMeasure_convPow (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ n : ℕ, IsProbabilityMeasure (convPow μ n)
  | 0 => by rw [convPow_zero]; infer_instance
  | (n + 1) => by
      have := isProbabilityMeasure_convPow μ n
      rw [convPow_succ]
      infer_instance

instance sfinite_convPow (μ : Measure ℝ) [SFinite μ] :
    ∀ n : ℕ, SFinite (convPow μ n)
  | 0 => by rw [convPow_zero]; infer_instance
  | (n + 1) => by
      have := sfinite_convPow μ n
      rw [convPow_succ]
      infer_instance

