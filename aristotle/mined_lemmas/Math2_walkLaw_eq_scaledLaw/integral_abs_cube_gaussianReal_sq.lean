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

theorem integral_abs_cube_gaussianReal_sq (c : ℝ) :
    ∫ x, |x| ^ 3 ∂(gaussianReal 0 (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0)) = |c| ^ 3 * gaussThirdMoment := by
  rw [gaussianReal_eq_map c, integral_abs_cube_map_const_mul, gaussThirdMoment]

end Gaussian

/-- **Quantitative CLT.** If `μ` is a centered probability measure on `ℝ` with unit variance and
finite third absolute moment, then the law of `c * (X₁ + ⋯ + X_m)` (`Xᵢ` iid with law `μ`) is
close to the centered Gaussian of variance `m * c ^ 2` when tested against a smooth test
function. -/
