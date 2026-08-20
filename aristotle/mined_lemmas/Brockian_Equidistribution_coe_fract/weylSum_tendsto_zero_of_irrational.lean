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
Weyl's criterion for equidistribution modulo one, and its application to the
sequence `n ↦ n • α` for irrational `α`.
-/
import Mathlib

open Filter MeasureTheory Metric Set Submodule
open scoped Topology Real

namespace Brockian.Equidistribution

noncomputable section

/-! ## Definitions -/

/-- A sequence `u : ℕ → ℝ` is *equidistributed modulo one* if for every subinterval
`[a, b) ⊆ [0, 1]` the proportion of the first `N` terms whose fractional part lies in `[a, b)`
tends to `b - a`. -/

theorem weylSum_tendsto_zero_of_irrational {α : ℝ} (hα : Irrational α) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (weylSum (fun n : ℕ => n * α) h) atTop (𝓝 0) := by
  set q : ℂ := Complex.exp (2 * Real.pi * Complex.I * h * α) with hqdef
  have hq1 : q ≠ 1 := by
    intro hcon
    rw [hqdef, Complex.exp_eq_one_iff] at hcon
    obtain ⟨n, hn⟩ := hcon
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hc : (h : ℂ) * α = n := by
      field_simp at hn ⊢
      linear_combination hn
    have hreal : (h : ℝ) * α = n := by exact_mod_cast hc
    exact (hα.intCast_mul hh).ne_int n hreal
  have hnorm : ‖q‖ = 1 := by
    rw [hqdef, Complex.norm_exp]
    have hre : (2 * (Real.pi : ℂ) * Complex.I * h * α).re = 0 := by simp
    rw [hre]
    simp
  have hq0 : (0 : ℝ) < ‖q - 1‖ := by simpa [sub_eq_zero] using hq1
  have hbound : ∀ N : ℕ, ‖weylSum (fun n : ℕ => n * α) h N‖ ≤ (N : ℝ)⁻¹ * (2 / ‖q - 1‖) := by
    intro N
    have hsum : ∑ k ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * h * (((k : ℝ) * α : ℝ) : ℂ))
        = (q ^ N - 1) / (q - 1) := by
      rw [← geom_sum_eq hq1]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast; ring
    simp only [weylSum]
    rw [hsum, norm_mul, norm_inv, Complex.norm_natCast, norm_div]
    have h2 : ‖q ^ N - 1‖ ≤ 2 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_pow, hnorm]
      norm_num
    gcongr
  refine squeeze_zero_norm hbound ?_
  simpa using tendsto_inv_atTop_nhds_zero_nat.mul_const (2 / ‖q - 1‖)

/-- A sanity check showing that `IsEquidistributedMod1` is a nontrivial condition:
the constant sequence `0` is not equidistributed modulo one. -/
