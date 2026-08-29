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

private theorem conv_swap_right (a b c : Measure ℝ) [SFinite a] [SFinite b] [SFinite c] :
    (a ∗ b) ∗ c = (a ∗ c) ∗ b := by
  rw [Measure.conv_assoc, Measure.conv_comm b c, ← Measure.conv_assoc]

/-- The Lindeberg telescoping estimate: convolution powers of two probability measures with the
same first two moments have close integrals against a smooth test function. -/
