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

theorem walk_gaussian_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    {f f1 f2 f3 : ℝ → ℝ} {M : ℝ} (h : IsC3Test f f1 f2 f3 M) (c : ℝ) (m : ℕ) :
    |(∫ x, f x ∂((convPow μ m).map (fun x => c * x)))
        - ∫ x, f x ∂(gaussianReal 0 (m • (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0)))|
      ≤ m * (M * (|c| ^ 3 * ((∫ x, |x| ^ 3 ∂μ) + gaussThirdMoment))) := by
  set P : Measure ℝ := μ.map (fun x => c * x) with hP
  set Q : Measure ℝ := gaussianReal 0 (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0) with hQ
  have hP1 : ∫ x, x ∂P = 0 := by rw [hP, integral_id_map_const_mul, hmean, mul_zero]
  have hQ1 : ∫ x, x ∂Q = 0 := integral_id_gaussianReal
  have hPQ2 : ∫ x, x ^ 2 ∂P = ∫ x, x ^ 2 ∂Q := by
    rw [hP, hQ, integral_sq_map_const_mul, hvar, integral_sq_gaussianReal]
    simp
  have hP3 : Integrable (fun x : ℝ => |x| ^ 3) P := integrable_abs_cube_map_const_mul μ c h3
  have hQ3 : Integrable (fun x : ℝ => |x| ^ 3) Q := integrable_abs_cube_gaussianReal _
  have hPpow : convPow P m = (convPow μ m).map (fun x => c * x) := by
    have := map_convPow (AddMonoidHom.mulLeft c) (measurable_const_mul c) μ m
    simpa [hP] using this.symm
  have hQpow : convPow Q m = gaussianReal 0 (m • (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0)) := by
    rw [hQ, convPow_gaussianReal]
  have key := h.convPow_swap_bound hP1 hQ1 hPQ2 hP3 hQ3 m (Measure.dirac 0)
  rw [Measure.dirac_zero_conv, Measure.dirac_zero_conv, hPpow, hQpow] at key
  refine key.trans ?_
  have hm3P : ∫ x, |x| ^ 3 ∂P = |c| ^ 3 * ∫ x, |x| ^ 3 ∂μ := integral_abs_cube_map_const_mul μ c
  have hm3Q : ∫ x, |x| ^ 3 ∂Q = |c| ^ 3 * gaussThirdMoment := integral_abs_cube_gaussianReal_sq c
  rw [hm3P, hm3Q]
  apply le_of_eq
  ring

end Math2

import RequestProject.Limit
import RequestProject.SmoothStep

/-!
# From smooth test functions to convergence in distribution

Using the smooth step functions of `SmoothStep.lean` we upgrade the convergence of integrals of
smooth test functions to the convergence of the distribution functions, and then to convergence
in distribution (weak convergence of the laws).
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BoundedContinuousFunction

section CDF

/-- A finite measure without atoms puts small mass on small windows. -/
