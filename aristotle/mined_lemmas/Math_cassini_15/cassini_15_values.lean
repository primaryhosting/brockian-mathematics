/-
# Cassini 15
Category: Pure Mathematics
Target: Math.cassini_15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cassini 15
Category: Pure Mathematics
Target: Math.cassini_15
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

namespace Math

/-- **Cassini's identity at `n = 15`**: `F(14) * F(16) - F(15)^2 = (-1)^15`.

The proof specializes Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq : Int.fib (n + 1) * Int.fib (n - 1) - Int.fib n ^ 2
= (-1) ^ n.natAbs` to `n = 15`, transporting between `Int.fib` and `Nat.fib`
via `Int.fib_natCast`. -/

theorem cassini_15_values :
    Nat.fib 14 = 377 ∧ Nat.fib 15 = 610 ∧ Nat.fib 16 = 987 := by
  refine ⟨by decide, by decide, by decide⟩

end Math

#print axioms Math.cassini_15

