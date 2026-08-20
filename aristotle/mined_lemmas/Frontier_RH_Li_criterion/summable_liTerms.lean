/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
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

namespace Frontier

open Complex Filter

/-!
## Elementary complex-analytic estimates
-/

/-- Geometric bound: `|1 - r ^ n| ≤ n |1 - r| max(1,r) ^ n` for real `r ≥ 0`. -/

theorem summable_liTerms {z : ℕ → ℂ} (hd : Summable fun k => 1 - (z k).re)
    (he : Summable fun k => max 0 (‖z k‖ - 1)) (n : ℕ) :
    Summable fun k => (1 - (z k) ^ n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set E : ℝ := ∑' k, max 0 (‖z k‖ - 1) with hE
  have hEk : ∀ k, max 0 (‖z k‖ - 1) ≤ E := fun k => he.le_tsum k fun i _ => le_max_left _ _
  have hE0 : 0 ≤ E := le_trans (le_max_left 0 _) (hEk 0)
  refine Summable.of_norm_bounded
    (g := fun k => (2 * (n : ℝ) ^ 2 * (1 + E) ^ n) * liMajorant z k)
    ((summable_liMajorant hd he).mul_left _) fun k => ?_
  have hmb := master_bound (z k) n hn
  have hnorm : ‖(1 - (z k) ^ n).re‖ = |1 - ((z k) ^ n).re| := by
    simp [Real.norm_eq_abs]
  rw [hnorm]
  refine hmb.trans ?_
  have hstep : (1 + max 0 (‖z k‖ - 1)) ^ n ≤ (1 + E) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith [hEk k]) n
  have h2 : 2 * (n : ℝ) ^ 2 * (1 + max 0 (‖z k‖ - 1)) ^ n ≤ 2 * (n : ℝ) ^ 2 * (1 + E) ^ n :=
    mul_le_mul_of_nonneg_left hstep (by positivity)
  have h3 := mul_le_mul_of_nonneg_right h2 (liMajorant_nonneg z k)
  simpa [liMajorant] using h3

/-- Easy direction: if all `z k` lie in the closed unit disc then all Li sums are `≥ 0`. -/
