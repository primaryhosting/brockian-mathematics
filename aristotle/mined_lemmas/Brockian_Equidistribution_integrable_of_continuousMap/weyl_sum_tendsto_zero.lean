import Brockian.Equidistribution

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
# Weyl equidistribution

This file develops, from scratch, Weyl's criterion for equidistribution modulo one and applies
it to the sequence `n ↦ n * α` for irrational `α`.

The main statement is `Brockian.Equidistribution.equidistribution_of_asymptotic_exists`, which
is *conditional* on the asymptotic vanishing of the Weyl exponential sums, and its unconditional
consequence `Brockian.Equidistribution.equidistributedMod1_natMul_irrational`.
-/

namespace Brockian.Equidistribution

open MeasureTheory Filter Finset Complex Topology Metric

open scoped Real

noncomputable section

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem weyl_sum_tendsto_zero {α : ℝ} (hα : Irrational α) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * (n * α))) atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * π * Complex.I * h * α) with hz
  have hz1 : z ≠ 1 := by
    rw [hz, Ne, Complex.exp_eq_one_iff]
    rintro ⟨n, hn⟩
    have hpi : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.ext_iff]
    have h2 : ((h : ℂ) * α) * (2 * (π : ℂ) * Complex.I) = (n : ℂ) * (2 * (π : ℂ) * Complex.I) := by
      rw [← hn]; ring
    have h3 : ((h : ℂ) * α) = (n : ℂ) := mul_right_cancel₀ hpi h2
    have h4 : ((h : ℝ) * α) = (n : ℝ) := by exact_mod_cast h3
    have hh' : ((h : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hh
    exact hα.ne_rational n h (by field_simp at h4 ⊢; linarith [h4])
  have hznorm : ‖z‖ = 1 := by
    rw [hz, Complex.norm_exp]
    norm_num
  have hsum : ∀ N : ℕ, ∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * (n * α)) = (z ^ N - 1) / (z - 1) := by
    intro N
    rw [← geom_sum_eq hz1]
    exact Finset.sum_congr rfl fun n _ => by rw [hz, ← Complex.exp_nat_mul]; ring_nf
  have hzsub : (0 : ℝ) < ‖z - 1‖ := by simpa [sub_eq_zero] using hz1
  refine squeeze_zero_norm (a := fun N : ℕ => (2 / ‖z - 1‖) / N) (fun N => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [hsum N, norm_mul, norm_div, norm_inv, Complex.norm_natCast]
  have h5 : ‖z ^ N - 1‖ ≤ 2 :=
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hznorm]; norm_num
  calc (N : ℝ)⁻¹ * (‖z ^ N - 1‖ / ‖z - 1‖) ≤ (N : ℝ)⁻¹ * (2 / ‖z - 1‖) := by gcongr
    _ = (2 / ‖z - 1‖) / N := by ring

/-! ### Main results -/

/-- **Weyl's equidistribution theorem, conditional form.** If the Weyl exponential sums of the
sequence `n ↦ n * α` have vanishing averages, then the sequence is equidistributed modulo one. -/
