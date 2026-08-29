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

/-!
# Cassini
Category: Fibonacci
Target: Fibonacci.cassini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Fibonacci

/-- **Cassini's identity** for the Fibonacci numbers, stated over `ℤ` to avoid
truncated subtraction: for every `n : ℕ`,
`fib (n+2) * fib n - fib (n+1) ^ 2 = (-1) ^ (n+1)`.
Proved by induction on `n` using `Nat.fib_add_two`.

Mathlib also has a closely related statement for the integer-indexed Fibonacci
function: `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hk : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := k))
      have h3 : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := k + 1))
      have hp : ((-1 : ℤ)) ^ (k + 2) = -((-1 : ℤ) ^ (k + 1)) := by ring
      rw [hk] at ih
      rw [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl, h3, hk, hp]
      linear_combination -ih

end Fibonacci

#print axioms Fibonacci.cassini

