import Brockian.EquidistributionBVReduction

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

import Mathlib

/-!
# Equidistribution of `n • α` and the reduction of configuration counts to the main term

For an irrational `α`, the configuration count

`configCount α a b N = #{ n < N : Int.fract (n * α) ∈ [a, b) }`

is asymptotic to its main term `mainTerm a b N = (b - a) * N`.

The analytic input (Weyl equidistribution of the sequence `n • α` on the circle `ℝ / ℤ`)
is proved here from scratch, so the final statement
`configCount_over_main_tendsto` is unconditional.

The proof proceeds by:
* computing the Birkhoff averages of the Fourier monomials `fourier k` along the orbit
  (geometric sums, `avg_fourier_tendsto`);
* extending to all continuous functions by Stone--Weierstrass (`avg_continuous_tendsto`);
* sandwiching the indicator of an arc between continuous piecewise-linear functions
  (a bounded-variation reduction) to obtain the counting asymptotics.
-/

open Filter MeasureTheory Set Topology Complex
open scoped BigOperators

set_option autoImplicit false

namespace Brockian

namespace EquidistributionBVReduction

noncomputable section

local instance isProbabilityMeasure_volume_unitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- The point `n * α` of the circle `ℝ / ℤ`. -/

theorem avg_fourier_tendsto_zero {alpha : ℝ} (halpha : Irrational alpha) {k : ℤ} (hk : k ≠ 0) :
    Tendsto (avg alpha (fourier (T := 1) k)) atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * k * alpha) with hz
  have hpow : ∀ n : ℕ, fourier (T := 1) k (orbit alpha n) = z ^ n := by
    intro n
    rw [orbit, fourier_coe_apply, hz, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    have h4 : ((k : ℂ) * alpha) * (2 * Real.pi * Complex.I)
        = (m : ℂ) * (2 * Real.pi * Complex.I) := by rw [← hm]; ring
    have h3 : (k : ℂ) * alpha = m := mul_right_cancel₀ h2 h4
    have hkey : (k : ℝ) * alpha = m := by exact_mod_cast h3
    have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have halp : alpha = (m : ℝ) / (k : ℝ) := by field_simp; linarith [hkey]
    exact halpha ⟨(m : ℚ) / (k : ℚ), by push_cast [halp]; ring⟩
  have hznorm : ‖z‖ = 1 := by rw [hz, Complex.norm_exp]; norm_num
  have hnorm : ∀ N : ℕ, ‖avg alpha (fourier (T := 1) k) N‖ ≤ (N : ℝ)⁻¹ * (2 / ‖z - 1‖) := by
    intro N
    rw [avg, norm_smul, norm_inv, Real.norm_natCast]
    have hsum : ‖∑ n ∈ Finset.range N, fourier (T := 1) k (orbit alpha n)‖ ≤ 2 / ‖z - 1‖ := by
      simp only [hpow]
      rw [geom_sum_eq hz1, norm_div]
      gcongr
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by simp [norm_pow, hznorm]; norm_num
    have hpos : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left hsum hpos
  refine squeeze_zero_norm hnorm ?_
  have h0 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa using h0.mul_const (2 / ‖z - 1‖)

/-- The Birkhoff averages of a Fourier monomial along the orbit of an irrational rotation
converge to the integral of the monomial. -/
