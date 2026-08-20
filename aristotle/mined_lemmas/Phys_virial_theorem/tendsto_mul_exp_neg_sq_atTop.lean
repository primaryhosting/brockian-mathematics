/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Statement: For a bound stationary state, 2⟨T⟩ = ⟨r·∇V⟩ (quantum virial theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology

namespace Phys

/-- **Auxiliary integration-by-parts fact.**  If `f` is everywhere differentiable with
integrable derivative `f'` and `f` tends to `0` at both ends of the real line, then the
integral of `f'` over `ℝ` vanishes. -/

theorem tendsto_mul_exp_neg_sq_atTop :
    Tendsto (fun x : ℝ => x * Real.exp (-x ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun u : ℝ => u ^ 1 * Real.exp (-u)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  refine squeeze_zero_norm' ?_ (by simpa using h)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  have hle : Real.exp (-x ^ 2) ≤ Real.exp (-x) := by
    apply Real.exp_le_exp.2; nlinarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx0, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left hle hx0

