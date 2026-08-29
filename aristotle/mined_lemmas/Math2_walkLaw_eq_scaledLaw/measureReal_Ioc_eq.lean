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

private theorem measureReal_Ioc_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] {a b : ℝ}
    (hab : a ≤ b) : ν.real (Ioc a b) = ν.real (Iic b) - ν.real (Iic a) := by
  have : ν.real (Iic b) = ν.real (Iic a) + ν.real (Ioc a b) := by
    rw [← measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic hab]
  linarith

/-- The law of `S_p / √n`, as a probability measure. -/
