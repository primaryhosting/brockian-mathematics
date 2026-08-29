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

theorem map_convPow (L : ℝ →+ ℝ) (hL : Measurable L) (μ : Measure ℝ) [SFinite μ] (n : ℕ) :
    (convPow μ n).map L = convPow (μ.map L) n := by
  induction n with
  | zero => simp [Measure.map_dirac hL]
  | succ n ih =>
      rw [convPow_succ, Measure.map_conv_addMonoidHom L hL, ih, convPow_succ]

/-- Convolution powers of a centered Gaussian. -/
