import Mathlib

/-!
# Simple Zero Shadow
Category: Riemann Program
Target: Riemann.Method.simple_zero_shadow
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

namespace Riemann.Method

/-- **Simple zero shadow (Montgomery's integrality step).**

For every natural number `m` with `1 ≤ m` we have `2 * m ≤ m ^ 2 + 1`, with equality
if and only if `m = 1`.  This is exactly the inequality `(m - 1) ^ 2 ≥ 0`, the step that
separates simple zeros in the two-thirds argument. -/
theorem simple_zero_shadow (m : ℕ) (hm : 1 ≤ m) :
    2 * m ≤ m ^ 2 + 1 ∧ (2 * m = m ^ 2 + 1 ↔ m = 1) := by
  constructor
  · -- `(m - 1) ^ 2 ≥ 0`, i.e. `Mathlib`'s `sq_nonneg`, expanded via `m - 1 + 1 = m`.
    nlinarith [Nat.sub_add_cancel hm, sq_nonneg (m - 1)]
  · constructor
    · intro h
      nlinarith [Nat.sub_add_cancel hm]
    · rintro rfl
      norm_num

end Riemann.Method

