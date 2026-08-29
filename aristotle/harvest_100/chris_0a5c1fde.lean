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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann
namespace Method

/-- **Simple Zero Shadow** (Montgomery's `(m - 1)^2 ≥ 0` integrality step).

For every natural number `m` with `1 ≤ m` we have `2 * m ≤ m ^ 2 + 1`, with
equality exactly when `m = 1`.

The inequality is just the expansion of `(m - 1)^2 ≥ 0` (over an ordered ring
this is Mathlib's `two_mul_le_add_sq`); here everything is stated over ℕ, where
the hypothesis `1 ≤ m` is in fact not needed for the inequality itself. -/
theorem simple_zero_shadow (m : ℕ) (hm : 1 ≤ m) :
    2 * m ≤ m ^ 2 + 1 ∧ (2 * m = m ^ 2 + 1 ↔ m = 1) := by
  refine ⟨by nlinarith [sq_nonneg m], ?_, ?_⟩
  · intro h
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · omega
    · exfalso; nlinarith
  · rintro rfl
    norm_num

end Method
end Riemann

