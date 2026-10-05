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

theorem lipschitz_f2 (h : IsC3Test f f1 f2 f3 M) (x y : ℝ) :
    |f2 y - f2 x| ≤ M * |y - x| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f2) (f' := f3)
    (s := univ) (fun z _ => (h.hasDeriv2 z).hasDerivWithinAt) (fun z _ => by
      simpa [Real.norm_eq_abs] using h.bound3 z) convex_univ (mem_univ x) (mem_univ y)
  simpa [Real.norm_eq_abs] using this

/-- The crude third order Taylor estimate. -/
