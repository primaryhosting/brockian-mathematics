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

theorem finite_large_norm {z : ℕ → ℂ} (he : Summable fun k => max 0 (‖z k‖ - 1)) {η : ℝ}
    (hη : 0 < η) : {k | 1 + η ≤ ‖z k‖}.Finite := by
  have h0 := he.tendsto_cofinite_zero
  have h1 : ∀ᶠ k in cofinite, max 0 (‖z k‖ - 1) < η := h0 (Iio_mem_nhds hη)
  rw [Filter.eventually_cofinite] at h1
  refine Set.Finite.subset h1 fun k hk => ?_
  simp only [Set.mem_setOf_eq] at hk ⊢
  push_neg
  have h2 : η ≤ ‖z k‖ - 1 := by linarith
  exact h2.trans (le_max_right _ _)

/-- If some member of the family lies outside the closed unit disc, the supremum of the norms
is attained. -/
