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

noncomputable def brownianFdd (t : ℕ → ℝ) (k : ℕ) : Measure (Fin k → ℝ) :=
  (brownianIncrements t k).map (partialSumMap k)

instance isProbabilityMeasure_brownianFdd (t : ℕ → ℝ) (k : ℕ) :
    IsProbabilityMeasure (brownianFdd t k) := by
  rw [brownianFdd]
  exact (brownianIncrements t k).isProbabilityMeasure_map
    (measurable_partialSumMap k).aemeasurable

/-- Summing consecutive blocks recovers the partial sum over the whole range. -/
