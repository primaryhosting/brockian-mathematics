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

theorem liMajorant_nonneg (z : ℕ → ℂ) (k : ℕ) : 0 ≤ liMajorant z k := by
  have h1 : (z k).re ≤ ‖z k‖ := Complex.re_le_norm _
  have h2 : ‖z k‖ - 1 ≤ max 0 (‖z k‖ - 1) := le_max_right _ _
  have h3 : (0 : ℝ) ≤ max 0 (‖z k‖ - 1) := le_max_left _ _
  simp only [liMajorant]
  linarith

