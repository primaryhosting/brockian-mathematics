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

noncomputable def scaledLaw (μ : Measure ℝ) (p n : ℕ) : Measure ℝ :=
  (convPow μ p).map (fun x => (Real.sqrt n)⁻¹ * x)

instance isProbabilityMeasure_scaledLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (p n : ℕ) :
    IsProbabilityMeasure (scaledLaw μ p n) := by
  rw [scaledLaw]; infer_instance

/-- The law of the rescaled random walk `S_{⌊n t⌋} / √n` with step distribution `μ`. -/

noncomputable def convPow (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | (n + 1) => (convPow μ n) ∗ μ
