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

theorem liSumOf_nonneg_of_norm_le_one {z : ℕ → ℂ} (h : ∀ k, ‖z k‖ ≤ 1) (n : ℕ) :
    0 ≤ liSumOf z n := by
  refine tsum_nonneg fun k => ?_
  have h1 : ((z k) ^ n).re ≤ ‖(z k) ^ n‖ := Complex.re_le_norm _
  have h2 : ‖(z k) ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (h k)
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- Only finitely many members of the family can have norm `≥ 1 + η`. -/
