import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

namespace Brockian.Equidistribution

open MeasureTheory Filter Topology Metric Finset

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

/-! ### Cesàro averages along a sequence -/

/-- The Cesàro average of a function `f` on the circle `ℝ/ℤ` along the first `N` terms of a
real sequence `x`. -/

lemma weyl_sums_tendsto_zero_of_irrational {α : ℝ} (hα : Irrational α) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * h * (((n : ℝ) * α : ℝ) : ℂ))) atTop (𝓝 0) := by
  set w : ℂ := Complex.exp (2 * Real.pi * Complex.I * h * α) with hwdef
  have hwn : ‖w‖ = 1 := by rw [hwdef, Complex.norm_exp]; norm_num
  have hw1 : w ≠ 1 := by
    intro hcon
    rw [hwdef, Complex.exp_eq_one_iff] at hcon
    obtain ⟨k, hk⟩ := hcon
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h3 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    have h2 : (2 : ℂ) * Real.pi * Complex.I * ((h : ℂ) * α)
        = (2 : ℂ) * Real.pi * Complex.I * k := by
      rw [show (2 : ℂ) * Real.pi * Complex.I * ((h : ℂ) * α)
            = 2 * Real.pi * Complex.I * h * α by ring, hk]
      ring
    have hc : (h : ℂ) * α = k := mul_left_cancel₀ h3 h2
    have hreal : (h : ℝ) * α = k := by exact_mod_cast hc
    have hirr : Irrational ((h : ℝ) * α) := hα.intCast_mul hh
    rw [hreal] at hirr
    exact (Rat.not_irrational k) (by exact_mod_cast hirr)
  have hterm : ∀ n : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * h * (((n : ℝ) * α : ℝ) : ℂ)) = w ^ n := by
    intro n
    rw [hwdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hd : 0 < ‖w - 1‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hw1
  have hbound : ∀ N : ℕ, ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I * h * (((n : ℝ) * α : ℝ) : ℂ))‖
      ≤ (2 / ‖w - 1‖) * (N : ℝ)⁻¹ := by
    intro N
    simp only [hterm]
    rw [geom_sum_eq hw1, norm_mul, norm_inv, Complex.norm_natCast, norm_div]
    have hnum : ‖w ^ N - 1‖ ≤ 2 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_pow, hwn]
      norm_num
    rw [mul_comm ((2 : ℝ) / ‖w - 1‖) ((N : ℝ)⁻¹)]
    exact mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hd).mpr hnum) (by positivity)
  refine squeeze_zero_norm hbound ?_
  simpa using tendsto_inv_atTop_nhds_zero_nat.const_mul (2 / ‖w - 1‖)

/-- **Weyl's theorem on irrational rotations**, an unconditional consequence of
`equidistribution_of_asymptotic`: for irrational `α`, the sequence `n * α` is equidistributed
modulo one. In particular the hypothesis of `equidistribution_of_asymptotic` is satisfiable. -/
