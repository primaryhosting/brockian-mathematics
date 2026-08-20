import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution: existence of the asymptotic average

This file develops Weyl's criterion for equidistribution modulo one on the circle
`AddCircle (1 : ℝ) = ℝ / ℤ`, and deduces from it Weyl's equidistribution theorem for the
sequence `n ↦ n * a` with `a` irrational.

Main results:

* `Brockian.Equidistribution.isEquidistributed_of_tendsto_fourier`: Weyl's criterion.
* `Brockian.Equidistribution.isEquidistributed_irrational`: the orbit of an irrational
  rotation is equidistributed mod 1.
* `Brockian.Equidistribution.equidistribution_of_asymptotic_exists`: unconditional statement
  that for irrational `a` the asymptotic average of any continuous function along `n * a`
  exists and equals the integral of the function.
-/

open MeasureTheory Filter Complex
open scoped Topology BigOperators

namespace Brockian.Equidistribution

local instance factZeroLtOne : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The Birkhoff-type average of a continuous function `f` on the circle `ℝ / ℤ` along the
first `N` points of the real sequence `x`, taken modulo `1`. -/

lemma tendsto_avg_fourier_irrational {a : ℝ} (ha : Irrational a) (k : ℤ) (hk : k ≠ 0) :
    Tendsto (avg (fun n : ℕ => (n : ℝ) * a) (fourier k)) atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * Real.pi * I * k * a) with hz
  have hzn : ∀ n : ℕ, (fourier k) (((n : ℝ) * a : ℝ) : AddCircle (1 : ℝ)) = z ^ n := by
    intro n
    rw [fourier_coe_apply, hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hzabs : ‖z‖ = 1 := by
    rw [hz, Complex.norm_exp]
    simp [Complex.re_ofNat]
  have hzne : z ≠ 1 := exp_two_pi_I_ne_one ha hk
  have hsub : ‖z - 1‖ > 0 := by simpa [sub_eq_zero] using hzne
  refine squeeze_zero_norm (a := fun N : ℕ => (N : ℝ)⁻¹ * (2 / ‖z - 1‖)) (fun N => ?_) ?_
  · have hsum : ∑ n ∈ Finset.range N, (fourier k) (((n : ℝ) * a : ℝ) : AddCircle (1 : ℝ))
        = (z ^ N - 1) / (z - 1) := by
      rw [Finset.sum_congr rfl fun n _ => hzn n, geom_sum_eq hzne]
    rw [avg]
    simp only [hsum, norm_mul, norm_div, norm_inv, Complex.norm_natCast]
    have hnum : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hzabs]; norm_num
    have hdiv : ‖z ^ N - 1‖ / ‖z - 1‖ ≤ 2 / ‖z - 1‖ := by gcongr
    exact mul_le_mul_of_nonneg_left hdiv (by positivity)
  · have h1 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using h1.mul_const (2 / ‖z - 1‖)

/-- **Weyl's equidistribution theorem**: for irrational `a`, the sequence `n ↦ n * a` is
equidistributed mod 1. -/
