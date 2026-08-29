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

private theorem abs_le_abs_of_mem_uIcc {u v : ℝ} (hv : v ∈ Set.uIcc (0 : ℝ) u) : |v| ≤ |u| := by
  have hu1 := le_abs_self u
  have hu2 := neg_abs_le u
  rcases Set.mem_uIcc.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [abs_le] <;> constructor <;> linarith

/-- Mean value bound for the second derivative. -/
