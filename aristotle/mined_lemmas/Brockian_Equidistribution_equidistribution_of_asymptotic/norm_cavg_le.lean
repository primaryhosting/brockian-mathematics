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

lemma norm_cavg_le (x : ℕ → ℝ) (f : C(𝕋, ℂ)) (N : ℕ) : ‖cavg x f N‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cavg, norm_nonneg]
  · rw [cavg, norm_mul, norm_inv, Complex.norm_natCast]
    have h1 : ‖∑ n ∈ Finset.range N, f ((x n : ℝ) : 𝕋)‖ ≤ N * ‖f‖ := by
      calc ‖∑ n ∈ Finset.range N, f ((x n : ℝ) : 𝕋)‖
          ≤ ∑ n ∈ Finset.range N, ‖f ((x n : ℝ) : 𝕋)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ := Finset.sum_le_sum (fun _ _ => f.norm_coe_le_norm _)
        _ = N * ‖f‖ := by simp
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN
    rw [inv_mul_le_iff₀ hNpos]
    exact h1

