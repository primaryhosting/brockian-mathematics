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

theorem map_rescaledWalk (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = μ) (n : ℕ) (t : ℝ) :
    P.map (rescaledWalk X n t) = walkLaw μ n t := by
  have hsum : Measurable fun ω => ∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω :=
    Finset.measurable_sum _ fun i _ => hmeas i
  have hcomp : rescaledWalk X n t
      = (fun x : ℝ => (Real.sqrt n)⁻¹ * x) ∘
        (fun ω => ∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) := by
    funext ω
    simp [rescaledWalk, Function.comp, div_eq_inv_mul]
  rw [hcomp, ← Measure.map_map (by fun_prop) hsum,
    map_partialSum_eq_convPow hmeas hindep hident, walkLaw, scaledLaw]

/-- **Donsker's invariance principle (one-dimensional marginals).**

Let `X 0, X 1, …` be an i.i.d. sequence of real random variables with common law `μ`, which is
centred (`∫ y ∂μ = 0`), has unit variance (`∫ y² ∂μ = 1`) and a finite third absolute moment.
Write `S_m = X 0 + ⋯ + X (m-1)` for the random walk.  Then for every time `t ≥ 0` the rescaled
walk `S_{⌊n t⌋} / √n` converges in distribution, as `n → ∞`, to the value at time `t` of a
standard Brownian motion, i.e. to the centred Gaussian law with variance `t`.

Convergence in distribution is stated in two equivalent standard forms: convergence of the
distribution functions at every point, and convergence of the expectations of every bounded
continuous test function. -/
