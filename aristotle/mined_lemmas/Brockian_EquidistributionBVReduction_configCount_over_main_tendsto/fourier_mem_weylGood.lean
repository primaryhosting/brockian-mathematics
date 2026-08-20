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
# Equidistribution of irrational rotations and the BV reduction of configuration counts

This file proves, unconditionally, that for an irrational `α` the number of `n < N` with
`Int.fract (n * α)` in a window `[a, b) ⊆ [0, 1]` is asymptotic to the main term `(b - a) * N`.

The equidistribution input (Weyl's theorem for the sequence `n ↦ n α mod 1`) is proved here from
scratch, via Weyl's criterion: the set of continuous test functions on the circle for which the
Birkhoff averages converge to the mean is a closed submodule containing all characters, hence is
everything, by density of trigonometric polynomials.  A bounded-variation ("BV") style sandwich by
continuous trapezoidal functions then transfers the statement to indicator functions of windows.
-/

open MeasureTheory Filter Set Metric Topology Complex
open scoped BigOperators

namespace Brockian.EquidistributionBVReduction

noncomputable section

/-- The number of `n < N` for which the fractional part of `n * α` lies in the window `[a, b)`. -/

theorem fourier_mem_weylGood (halpha : Irrational alpha) (k : ℤ) :
    (fourier k : C(AddCircle (1 : ℝ), ℂ)) ∈ weylGood alpha := by
  show Tendsto (circleAvg alpha (fourier k)) atTop (𝓝 _)
  rcases eq_or_ne k 0 with rfl | hk
  · rw [integral_fourier_zero]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    simp [circleAvg, div_self hN']
  · rw [integral_fourier_eq_zero hk]
    set z : ℂ := (fourier k) ((alpha : ℝ) : AddCircle (1 : ℝ)) with hzdef
    have hz1 : z ≠ 1 := by
      rw [hzdef, fourier_coe_apply]
      intro h
      rw [Complex.exp_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      have hpi : (2 : ℂ) * Real.pi * I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      field_simp at hn
      have hR : (k : ℝ) * alpha = (n : ℝ) := by
        exact_mod_cast (by simpa using hn : (k : ℂ) * alpha = n)
      have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
      refine halpha ⟨(n : ℚ) / (k : ℚ), ?_⟩
      push_cast
      field_simp
      linarith [hR]
    have hznorm : ‖z‖ = 1 := by
      rw [hzdef, fourier_coe_apply, Complex.norm_exp]
      norm_num
    have hterm : ∀ n : ℕ, (fourier k) ((n * alpha : ℝ) : AddCircle (1 : ℝ)) = z ^ n := by
      intro n
      rw [hzdef, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
    have hd : 0 < ‖z - 1‖ := by simpa [sub_eq_zero] using hz1
    have hbound : ∀ N : ℕ, ‖circleAvg alpha (fourier k) N‖ ≤ (2 / ‖z - 1‖) / N := by
      intro N
      have hsum : ∑ n ∈ Finset.range N, (fourier k) ((n * alpha : ℝ) : AddCircle (1 : ℝ))
          = (z ^ N - 1) / (z - 1) := by
        simp only [hterm]
        exact geom_sum_eq hz1 N
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp [circleAvg]
      · rw [circleAvg, hsum, norm_div, norm_div]
        have h1 : ‖z ^ N - 1‖ ≤ 2 := by
          calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_pow, hznorm]; norm_num
        have hcast : ‖(N : ℂ)‖ = (N : ℝ) := by simp
        rw [hcast]
        gcongr
    exact squeeze_zero_norm hbound (tendsto_const_div_atTop_nhds_zero_nat _)

/-- Birkhoff averages are `1`-Lipschitz in the sup norm of the test function. -/
