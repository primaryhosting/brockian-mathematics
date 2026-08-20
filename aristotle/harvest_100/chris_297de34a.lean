import Mathlib

/-!
# Cassini
Category: Fibonacci
Target: Fibonacci.cassini
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

/-- **Cassini's identity** for the Fibonacci numbers, stated over `ℤ` to avoid
truncated subtraction:
`fib (n+2) * fib n - fib (n+1) ^ 2 = (-1) ^ (n+1)`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h1 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
        simpa using Nat.fib_add_two (n := k + 1)
      have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      have h1' : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) h1
      have h2' : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) h2
      have hpow : ((-1 : ℤ)) ^ (k + 1 + 1) = -((-1 : ℤ)) ^ (k + 1) := by
        rw [pow_succ]; ring
      show (Nat.fib (k + 3) : ℤ) * (Nat.fib (k + 1) : ℤ) - (Nat.fib (k + 2) : ℤ) ^ 2
          = (-1) ^ (k + 1 + 1)
      rw [hpow, ← ih, h1', h2']
      ring

end Fibonacci

