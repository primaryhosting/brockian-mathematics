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

theorem integrable_abs_cube_map_const_mul (μ : Measure ℝ) (c : ℝ)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    Integrable (fun x : ℝ => |x| ^ 3) (μ.map (fun x => c * x)) := by
  rw [integrable_map_measure (by fun_prop) (measurable_const_mul c).aemeasurable]
  simp only [Function.comp_def, abs_mul, mul_pow]
  exact h3.const_mul _

instance isProbabilityMeasure_map_const_mul (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    IsProbabilityMeasure (μ.map (fun x => c * x)) :=
  Measure.isProbabilityMeasure_map (measurable_const_mul c).aemeasurable

end Scaling

section Gaussian

/-- The third absolute moment of a standard Gaussian. -/
