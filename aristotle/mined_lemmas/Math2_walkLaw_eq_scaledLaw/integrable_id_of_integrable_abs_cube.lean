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

theorem integrable_id_of_integrable_abs_cube (h3 : Integrable (fun x : ℝ => |x| ^ 3) P) :
    Integrable (fun x : ℝ => x) P := by
  refine Integrable.mono' (h3.add (integrable_const 1)) (by fun_prop) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [abs_nonneg x, sq_nonneg (|x| - 1), sq_nonneg (|x| + 1)]

