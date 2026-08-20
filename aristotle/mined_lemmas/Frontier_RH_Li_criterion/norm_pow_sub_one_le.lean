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

theorem norm_pow_sub_one_le (w : ℂ) (hw : ‖w‖ ≤ 1) (n : ℕ) : ‖w ^ n - 1‖ ≤ n * ‖w - 1‖ := by
  have h1 : ‖w ^ n - 1‖ = ‖1 - w ^ n‖ := by rw [← norm_neg]; congr 1; ring
  have h2 : ‖w - 1‖ = ‖1 - w‖ := by rw [← norm_neg]; congr 1; ring
  rw [h1, h2]
  exact norm_one_sub_pow_le w hw n

/-- For a unit complex number, `1 - Re (w ^ n) ≤ n ^ 2 (1 - Re w)`. -/
