import Mathlib
import RequestProject.SatoTate.Equidistribution

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above is placed directly after the `import` lines, since Lean 4 requires
`import` commands to come first in a file.)

## Contents

We formalise the Sato–Tate distribution of Frobenius angles of an elliptic curve over `ℚ`,
given by an integral Weierstrass model `W`.

* `Math2.frobAngle W p` is the Frobenius angle `θ_p ∈ [0, π]` at a prime `p`, defined by
  `a_p = 2 √p cos θ_p` where `a_p = p + 1 - #E(𝔽_p)` is the trace of Frobenius.
* `Math2.satoTateDensity` is the Sato–Tate density `(2/π) sin²θ` and `Math2.satoTateMeasure`
  is the associated probability measure on `[0, π]`.
* `Math2.SatoTateWeyl W` is the Weyl-criterion form of the Sato–Tate law: the averages over
  primes of good reduction of `U n (cos θ_p)` tend to `0` for every `n ≥ 1`, where `U n` is
  the `n`-th Chebyshev polynomial of the second kind (the character of the `n`-th symmetric
  power of the standard representation of `SU(2)`).  This is exactly the statement supplied
  by the potential automorphy theorems for a non-CM elliptic curve over `ℚ`.
* `Math2.sato_tate` deduces from it the distributional form of the Sato–Tate law: the
  proportion of primes `p ≤ N` of good reduction whose Frobenius angle lies in `[a, b]`
  converges to `(2/π) ∫_a^b sin²t dt`.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open Filter Topology MeasureTheory Set

/-- The number of points of the reduction of the integral Weierstrass model `W` modulo `p`
(including the point at infinity). -/

theorem tendsto_avg_continuous
    (hθ : ∀ p, θ p ∈ Icc 0 π)
    (hS : ∀ᶠ N in atTop, (S N).Nonempty)
    (hU : ∀ n : ℕ, 1 ≤ n →
      Tendsto (fun N => avg (S N) θ
        (fun t => (Polynomial.Chebyshev.U ℝ n).eval (Real.cos t))) atTop (𝓝 0))
    {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun N => avg (S N) θ f) atTop (𝓝 (∫ t, f t ∂satoTateMeasure)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε : ℝ := δ / 4 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-1) 1
    (fun x => f (Real.arccos x)) (Continuous.continuousOn (by fun_prop)) ε hε
  have hclose : ∀ t ∈ Icc (0:ℝ) π, |P.eval (Real.cos t) - f t| ≤ ε := by
    intro t ht
    have hcos : Real.cos t ∈ Icc (-1:ℝ) 1 := ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
    have h := hP (Real.cos t) hcos
    rw [Real.arccos_cos ht.1 ht.2] at h
    exact h.le
  have h1 : ∀ N, |avg (S N) θ f - avg (S N) θ (fun t => P.eval (Real.cos t))| ≤ ε := by
    intro N
    refine abs_avg_sub_avg_le hε.le (fun p _ => ?_)
    rw [abs_sub_comm]
    exact hclose (θ p) (hθ p)
  have h2 : |(∫ t, f t ∂satoTateMeasure) - ∫ t, P.eval (Real.cos t) ∂satoTateMeasure| ≤ ε := by
    rw [← MeasureTheory.integral_sub (integrable_of_continuous hf)
      (integrable_of_continuous (continuous_eval_cos P))]
    have hb : ∀ᵐ t ∂satoTateMeasure, ‖f t - P.eval (Real.cos t)‖ ≤ ε := by
      filter_upwards [satoTateMeasure_ae_mem_Icc] with t ht
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hclose t ht
    have := MeasureTheory.norm_integral_le_of_norm_le_const hb
    simpa using this
  have h3 := tendsto_avg_polynomial hS hU P
  rw [Metric.tendsto_atTop] at h3
  obtain ⟨N₀, hN₀⟩ := h3 ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have hmid := hN₀ N hN
  rw [Real.dist_eq] at hmid ⊢
  have t1 := abs_sub_le (avg (S N) θ f) (avg (S N) θ (fun t => P.eval (Real.cos t)))
    (∫ t, f t ∂satoTateMeasure)
  have t2 := abs_sub_le (avg (S N) θ (fun t => P.eval (Real.cos t)))
    (∫ t, P.eval (Real.cos t) ∂satoTateMeasure) (∫ t, f t ∂satoTateMeasure)
  have h2' : |(∫ t, P.eval (Real.cos t) ∂satoTateMeasure) - ∫ t, f t ∂satoTateMeasure| ≤ ε := by
    rw [abs_sub_comm]; exact h2
  have := h1 N
  linarith

/-- **Equidistribution from the Weyl criterion.** If the Chebyshev averages of a family of
angles in `[0, π]` tend to zero, then the proportion of angles lying in `[a, b]` tends to the
Sato–Tate measure of `[a, b]`, namely `(2/π) ∫_a^b sin²t dt`. -/
