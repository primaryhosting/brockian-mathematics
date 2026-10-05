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

theorem sTrans3_eq_zero_of_one_lt : ∀ y, (1 : ℝ) < y → sTrans3 y = 0 := by
  have h1 : ∀ y, (1 : ℝ) < y → sTrans1 y = 0 :=
    deriv_eq_zero_of_eventually_const_Ioi (c := 1)
      (fun y hy => Real.smoothTransition.one_of_one_le hy.le)
  have h2 : ∀ y, (1 : ℝ) < y → sTrans2 y = 0 :=
    deriv_eq_zero_of_eventually_const_Ioi (c := 0) h1
  exact deriv_eq_zero_of_eventually_const_Ioi (c := 0) h2

/-- The third derivative of the smooth transition function is bounded. -/
