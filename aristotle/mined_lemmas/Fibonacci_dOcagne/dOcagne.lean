import Mathlib

/-!
# D Ocagne
Category: Fibonacci
Target: Fibonacci.dOcagne
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

namespace Fibonacci

/-- **d'Ocagne's identity**, addition form (avoiding natural subtraction):
`F (m + n + 1) = F (m+1) * F (n+1) + F m * F n`. -/

theorem dOcagne (m n : ℕ) :
    (Nat.fib (m + n + 1) : ℤ) = Nat.fib (m + 1) * Nat.fib (n + 1) + Nat.fib m * Nat.fib n := by
  rw [Nat.fib_add]
  push_cast
  ring

/-- Shifted form of d'Ocagne's identity: for all `n d : ℕ`,
`F (n+d) * F (n+1) - F (n+d+1) * F n = (-1)^n * F d`. -/
