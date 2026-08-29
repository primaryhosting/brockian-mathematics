/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.
This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_nat_fib`). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 9`: `F 8 * F 10 - F 9 ^ 2 = (-1) ^ 9`. -/
theorem cassini_9 :
    (fib 8 : Int) * (fib 10 : Int) - (fib 9 : Int) ^ 2 = (-1) ^ 9 := by
  decide

end Math

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

import Mathlib
import RequestProject.Cassini9

/-!
# Cassini 9, stated with Mathlib's `Nat.fib`

The main statement lives in `RequestProject/Cassini9.lean`, whose file must begin with the
prescribed header comment (and hence cannot contain an `import`). Here we check that the
Fibonacci sequence used there coincides with Mathlib's `Nat.fib`, and restate the identity.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 9`, phrased with Mathlib's `Nat.fib`. -/
theorem cassini_9_nat_fib :
    (Nat.fib 8 : ℤ) * (Nat.fib 10 : ℤ) - (Nat.fib 9 : ℤ) ^ 2 = (-1) ^ 9 := by
  simpa [fib_eq_nat_fib] using cassini_9

end Math

