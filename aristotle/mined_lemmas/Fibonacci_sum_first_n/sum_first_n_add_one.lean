import Mathlib

/-!
# Sum First N
Category: Fibonacci
Target: Fibonacci.sum_first_n
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

/-- Auxiliary (subtraction-free) form: the sum of the first `n` Fibonacci numbers,
plus one, equals `fib (n+1)`. -/

theorem sum_first_n_add_one (n : ℕ) :
    (Finset.range n).sum (fun i => Nat.fib i) + 1 = Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Nat.fib_add_two]
      omega

/-- Sum of the first `n` Fibonacci numbers: `∑_{i < n} fib i = fib (n+1) - 1`. -/
