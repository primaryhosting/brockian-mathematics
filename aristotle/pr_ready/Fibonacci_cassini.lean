/-!
# Cassini
Category: Fibonacci
Target: Fibonacci.cassini
Statement: Cassini's identity: for every natural n, (Nat.fib (n+2)) * (Nat.fib n) + 1 = (Nat.fib (n+1))^2 when n is even, and (Nat.fib (n+1))^2 + 1 = (Nat.fib (n+2))*(Nat.fib n) when n is odd. State over integers to avoid truncation: for all n : Nat, (Nat.fib (n+2) : Int) * (Nat.fib n) - (Nat.fib (n+1))^2 = (-1)^(n+1). Prove by induction.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Fibonacci

/-- Cassini's identity, stated over the integers to avoid truncated subtraction:
`F(n+2) * F(n) - F(n+1)^2 = (-1)^(n+1)`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n) - (Nat.fib (n + 1)) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hfib : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
      have hfib2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      push_cast [hfib, hfib2] at ih ⊢
      ring_nf
      ring_nf at ih
      linarith [ih, pow_succ (-1 : ℤ) (k + 1)]

end Fibonacci


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

