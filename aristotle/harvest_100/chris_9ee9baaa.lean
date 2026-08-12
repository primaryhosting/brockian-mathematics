/-
# Simple Zero Shadow
Category: Riemann Program
Target: Riemann.Method.simple_zero_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simple Zero Shadow
Category: Riemann Program
Target: Riemann.Method.simple_zero_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Method

/-- **Simple Zero Shadow.**  For every natural number `m` with `1 ≤ m` we have
`2 * m ≤ m ^ 2 + 1`, with equality precisely when `m = 1`.
This is Montgomery's `(m - 1) ^ 2 ≥ 0` integrality step, which separates *simple*
zeros in the two-thirds argument.

The hypothesis `1 ≤ m` is kept as requested, although the conclusion in fact also
holds for `m = 0`, so the proof does not need it. -/
theorem simple_zero_shadow (m : ℕ) (hm : 1 ≤ m) :
    2 * m ≤ m ^ 2 + 1 ∧ (2 * m = m ^ 2 + 1 ↔ m = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · zify
    nlinarith [sq_nonneg ((m : ℤ) - 1)]
  · intro h
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · omega
    · exfalso
      nlinarith [h, h2]
  · rintro rfl
    norm_num

end Riemann.Method

import Mathlib

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

