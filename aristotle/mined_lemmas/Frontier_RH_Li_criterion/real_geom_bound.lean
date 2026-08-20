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

theorem real_geom_bound (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    |1 - r ^ n| ≤ n * |1 - r| * (max 1 r) ^ n := by
  have h : 1 - r ^ n = (1 - r) * ∑ i ∈ Finset.range n, r ^ i := by
    have h2 : (∑ i ∈ Finset.range n, r ^ i) * (r - 1) = r ^ n - 1 := geom_sum_mul r n
    linear_combination h2
  rw [h, abs_mul]
  have hM : (1 : ℝ) ≤ max 1 r := le_max_left _ _
  have hs : |∑ i ∈ Finset.range n, r ^ i| ≤ n * (max 1 r) ^ n := by
    calc |∑ i ∈ Finset.range n, r ^ i| ≤ ∑ i ∈ Finset.range n, |r ^ i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, (max 1 r) ^ n := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_pow, abs_of_nonneg hr]
        exact (pow_le_pow_left₀ hr (le_max_right _ _) i).trans
          (pow_le_pow_right₀ hM (Finset.mem_range.mp hi).le)
    _ = n * (max 1 r) ^ n := by simp
  calc |1 - r| * |∑ i ∈ Finset.range n, r ^ i| ≤ |1 - r| * (n * (max 1 r) ^ n) :=
        mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  _ = n * |1 - r| * (max 1 r) ^ n := by ring

/-- `‖1 - w ^ n‖ ≤ n ‖1 - w‖` for `‖w‖ ≤ 1`. -/
