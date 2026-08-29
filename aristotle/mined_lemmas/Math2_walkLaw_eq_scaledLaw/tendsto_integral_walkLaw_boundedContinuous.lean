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

theorem tendsto_integral_walkLaw_boundedContinuous {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {t : ℝ} (ht : 0 ≤ t) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ x, f x ∂(walkLaw μ n t)) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 t.toNNReal))) := by
  have h := tendsto_walkLaw_probabilityMeasure hmean hvar h3 ht
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h
  exact h f

end Math2

import RequestProject.Blocks
import RequestProject.Weak

/-!
# Finite dimensional distributions of the rescaled random walk

We prove that the finite dimensional distributions of the rescaled random walk converge to those
of Brownian motion: for times `0 = t 0 ≤ t 1 ≤ ⋯ ≤ t k` the random vector

`(S_{⌊n t 1⌋}/√n, …, S_{⌊n t k⌋}/√n)`

converges in distribution to the vector of partial sums of independent centered Gaussians with
variances `t (j+1) - t j`, that is, to `(B_{t 1}, …, B_{t k})` for a Brownian motion `B`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BoundedContinuousFunction

section Fdd

/-- Partial sums of a vector: `partialSumMap z j = z 0 + ⋯ + z j`. -/
