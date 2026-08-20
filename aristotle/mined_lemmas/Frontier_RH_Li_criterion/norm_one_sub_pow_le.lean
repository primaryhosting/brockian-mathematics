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

theorem norm_one_sub_pow_le (w : ℂ) (hw : ‖w‖ ≤ 1) (n : ℕ) : ‖1 - w ^ n‖ ≤ n * ‖1 - w‖ := by
  have h : 1 - w ^ n = (1 - w) * ∑ i ∈ Finset.range n, w ^ i := by
    have h2 : (∑ i ∈ Finset.range n, w ^ i) * (w - 1) = w ^ n - 1 := geom_sum_mul w n
    linear_combination h2
  rw [h, norm_mul]
  have hs : ‖∑ i ∈ Finset.range n, w ^ i‖ ≤ n := by
    calc ‖∑ i ∈ Finset.range n, w ^ i‖ ≤ ∑ i ∈ Finset.range n, ‖w ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, 1 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
    _ = n := by simp
  calc ‖1 - w‖ * ‖∑ i ∈ Finset.range n, w ^ i‖ ≤ ‖1 - w‖ * n :=
        mul_le_mul_of_nonneg_left hs (norm_nonneg _)
  _ = n * ‖1 - w‖ := by ring

/-- `‖w ^ n - 1‖ ≤ n ‖w - 1‖` for `‖w‖ ≤ 1`. -/
