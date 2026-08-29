import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Phys

open Complex MeasureTheory Filter Topology

/-- The expectation value `⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/

theorem gaussian_tendsto_atTop : Tendsto (fun x : ℝ => x * Real.exp (-x ^ 2)) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun x : ℝ => x⁻¹)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h1 : x ^ 2 ≤ Real.exp (x ^ 2) := by nlinarith [Real.add_one_le_exp (x ^ 2)]
    have he : (0 : ℝ) < Real.exp (x ^ 2) := Real.exp_pos _
    rw [Real.exp_neg, inv_eq_one_div, mul_one_div, div_le_iff₀ he]
    calc x = x⁻¹ * x ^ 2 := by field_simp
      _ ≤ x⁻¹ * Real.exp (x ^ 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
  · exact tendsto_inv_atTop_zero

