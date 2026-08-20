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

import Brockian.WeylEquidistribution

/-!
# Equidistribution: reduction of a configuration count to its main term

Fix an irrational number `a`, a point `c` on the circle `ℝ/ℤ` and a radius `r` with
`0 < r < 1/2`.  Call `n` *admissible* if the orbit point `n • a` lies within distance `r` of `c`
on `ℝ/ℤ`.  `configCount a c r N` counts the admissible `n < N`, and the expected main term is
`mainTerm r N = 2 * r * N` (the measure of the arc times the number of trials).

The main result `configCount_over_main_tendsto` states that the ratio of the count to the main
term tends to `1`.

The analytic input is Weyl's equidistribution theorem for continuous test functions, proved in
`Brockian.WeylEquidistribution`; the passage from continuous test functions to the (bounded
variation, indeed indicator) test function of an arc is done here by sandwiching the indicator
between two explicit continuous, piecewise-linear functions.
-/

open MeasureTheory Filter Topology Metric
open scoped BigOperators

namespace Brockian
namespace EquidistributionBVReduction

open Brockian.Weyl

noncomputable section

open scoped Classical in
/-- The number of `n < N` for which the orbit point `n • a` lies within distance `r` of `c`
on the circle `ℝ/ℤ`. -/

lemma weyl_sum_tendsto (a : ℝ) (ha : Irrational a) {m : ℤ} (hm : m ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, fourier m (pt a n))
      atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * π * I * m * a) with hz
  have hterm : ∀ n : ℕ, fourier m (pt a n) = z ^ n := by
    intro n
    rw [pt, fourier_coe_apply, hz, ← Complex.exp_nat_mul]
    push_cast; ring_nf
  have hzne : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨k, hk⟩ := h
    have hne : (2 * (π : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h2 : (2 * (π : ℂ) * I) * ((m : ℂ) * a) = (2 * (π : ℂ) * I) * (k : ℂ) := by
      linear_combination hk
    have h3 : (m : ℝ) * a = (k : ℝ) := by
      have := mul_left_cancel₀ hne h2
      exact_mod_cast this
    exact (ha.intCast_mul hm).ne_int k h3
  have hznorm : ‖z‖ = 1 := by rw [hz, Complex.norm_exp]; simp
  have hzz : (0 : ℝ) < ‖z - 1‖ := by simpa [sub_eq_zero] using hzne
  have hfun : (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, fourier m (pt a n))
      = fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, z ^ n := by
    funext N; simp_rw [hterm]
  rw [hfun]
  have hbound : ∀ N : ℕ, ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, z ^ n‖ ≤ (2 / ‖z - 1‖) / N := by
    intro N
    have key : ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
      rw [geom_sum_eq hzne, norm_div]
      gcongr
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hznorm]; norm_num
    calc ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, z ^ n‖
        = (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, z ^ n‖ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast]
      _ ≤ (N : ℝ)⁻¹ * (2 / ‖z - 1‖) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = (2 / ‖z - 1‖) / N := by ring
  exact squeeze_zero_norm hbound (tendsto_const_div_atTop_nhds_zero_nat _)

/-- Equidistribution holds for every element of the linear span of the characters. -/
