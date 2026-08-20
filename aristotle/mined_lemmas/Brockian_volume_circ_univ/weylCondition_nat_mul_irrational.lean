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
# Weyl's equidistribution criterion, via reduction of BV (indicator) test functions

This file proves the classical **Weyl criterion** (sufficiency direction):
if all nontrivial exponential sums along a real sequence `x : ℕ → ℝ` have vanishing
Cesàro averages, then `x` is equidistributed modulo one in the counting sense.

The proof proceeds by the *BV reduction*: the characteristic function of an interval
(a function of bounded variation) is squeezed between continuous trapezoidal functions
on the circle, and continuous functions on the circle are approximated uniformly by
trigonometric polynomials.

As an application, the sequence `n ↦ n * α` is equidistributed mod one for irrational `α`.
-/

open Filter Topology MeasureTheory Finset

namespace Brockian
namespace EquidistributionBVReduction

noncomputable section

open scoped Classical

instance factOnePos : Fact ((0:ℝ) < 1) := ⟨one_pos⟩

/-- The circle `ℝ / ℤ`. -/
abbrev Circ := AddCircle (1:ℝ)

/-- `x : ℕ → ℝ` is equidistributed modulo one: for every subinterval `[a, b) ⊆ [0,1]`,
the proportion of the first `N` terms whose fractional part lies in `[a, b)` tends to
`b - a`. -/

theorem weylCondition_nat_mul_irrational {α : ℝ} (hα : Irrational α) :
    WeylCondition (fun n : ℕ => n * α) := by
  intro k hk
  set z : ℂ := Complex.exp (2 * (Real.pi:ℂ) * Complex.I * k * α) with hz
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have h2 : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 := by
      simp [Complex.ext_iff, Real.pi_ne_zero]
    field_simp at hm
    have hreal : (k:ℝ) * α = (m:ℝ) := by exact_mod_cast hm
    exact (Irrational.intCast_mul hα hk).ne_int m hreal
  have hnorm : ‖z‖ = 1 := by
    rw [hz, show 2 * (Real.pi:ℂ) * Complex.I * k * α
        = ((2 * Real.pi * k * α : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hsum : ∀ N : ℕ,
      (∑ n ∈ Finset.range N,
        Complex.exp (2 * (Real.pi:ℂ) * Complex.I * k * ((((n:ℝ) * α : ℝ)) : ℂ)))
        = (z ^ N - 1) / (z - 1) := by
    intro N
    rw [← geom_sum_eq hz1 N]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hd : 0 < ‖z - 1‖ := by simpa [sub_eq_zero] using hz1
  apply squeeze_zero_norm' (a := fun N : ℕ => (2 / ‖z - 1‖) / N)
  · filter_upwards with N
    rw [norm_div, hsum N, norm_div, Complex.norm_natCast]
    have hzn : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hnorm]; norm_num
    gcongr
  · exact tendsto_const_div_atTop_nhds_zero_nat _

/-- **Weyl's theorem**: for irrational `α`, the sequence `n ↦ n α` is equidistributed mod one. -/
