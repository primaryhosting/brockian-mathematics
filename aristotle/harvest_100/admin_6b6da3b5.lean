/-!
# Integrality Three Halves
Category: Riemann Program
Target: Riemann.Method.integrality_three_halves
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Method

/-- **Integrality (three halves).** For every natural number `m`, `3 * m ≤ m ^ 2 + 2`.

Equivalently `m ^ 2 ≥ 3 * m - 2`, i.e. `(m - 1) * (m - 2) ≥ 0` over the integers.

The proof splits at `m = 3`: for `m ≥ 3` the monotonicity lemma
`Nat.mul_le_mul_right` gives `3 * m ≤ m * m` directly, and the three
remaining cases `m = 0, 1, 2` are decided. -/
theorem integrality_three_halves (m : Nat) : 3 * m ≤ m ^ 2 + 2 := by
  have h : 3 * m ≤ m * m + 2 := by
    rcases Nat.lt_or_ge m 3 with h | h
    · match m, h with
      | 0, _ => decide
      | 1, _ => decide
      | 2, _ => decide
    · have := Nat.mul_le_mul_right m h
      omega
  simpa [Nat.pow_succ, Nat.pow_zero] using h

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

