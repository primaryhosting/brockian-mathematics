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

theorem liSumOf_nonneg_iff {z : ℕ → ℂ} (hd : Summable fun k => 1 - (z k).re)
    (he : Summable fun k => max 0 (‖z k‖ - 1)) :
    (∀ k, ‖z k‖ ≤ 1) ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liSumOf z n :=
  ⟨fun h n _ => liSumOf_nonneg_of_norm_le_one h n, fun h => norm_le_one_of_liSumOf_nonneg hd he h⟩

/-!
## The Riemann zeta function
-/

/-- The set of nontrivial zeros of the Riemann zeta function, i.e. the zeros excluded from
the statement of `RiemannHypothesis` in Mathlib. -/
