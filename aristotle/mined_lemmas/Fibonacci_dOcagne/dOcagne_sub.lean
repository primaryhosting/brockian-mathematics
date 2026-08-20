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

theorem dOcagne_sub {m n : ℕ} (h : n ≤ m) :
    (Nat.fib m : ℤ) * Nat.fib (n + 1) - (Nat.fib (m + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib (m - n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using dOcagne_shifted n d

end Fibonacci

