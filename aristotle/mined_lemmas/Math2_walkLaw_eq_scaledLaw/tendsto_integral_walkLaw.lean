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

theorem tendsto_integral_walkLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    {f f1 f2 f3 : ℝ → ℝ} {M : ℝ} (h : IsC3Test f f1 f2 f3 M) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => ∫ x, f x ∂(walkLaw μ n t)) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 t.toNNReal))) :=
  tendsto_integral_scaledLaw hmean hvar h3 h (m := fun n => ⌊(n : ℝ) * t⌋₊)
    (tendsto_floor_div t ht)

end Math2

import RequestProject.Lindeberg

/-!
# A quantitative central limit theorem

Combining the Lindeberg swapping estimate with the scaling properties of convolution powers we
obtain: if `μ` is centered with unit variance and finite third absolute moment, then the law of
the rescaled sum of `m` independent `μ`-distributed steps is close, when tested against smooth
functions, to a centered Gaussian with variance `m * c ^ 2` (here `c` is the scaling factor,
which will be `1 / √n`).
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

section Scaling

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {c : ℝ}

