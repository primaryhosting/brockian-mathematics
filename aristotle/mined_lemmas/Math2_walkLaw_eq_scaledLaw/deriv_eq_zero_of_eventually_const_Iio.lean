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

private theorem deriv_eq_zero_of_eventually_const_Iio {g : ℝ → ℝ} (hg : ∀ y < (0 : ℝ), g y = 0) :
    ∀ y < (0 : ℝ), deriv g y = 0 := by
  intro y hy
  have hev : g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hy] with z hz using hg z hz
  rw [hev.deriv_eq]
  simp

