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

theorem tendsto_walkLaw_probabilityMeasure {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => walkProb μ n t) atTop (𝓝 (brownianProb t)) :=
  tendsto_scaledProb hmean hvar h3 (m := fun n => ⌊(n : ℝ) * t⌋₊) (tendsto_floor_div t ht)

/-- **Donsker-type convergence tested against bounded continuous functions.** -/
