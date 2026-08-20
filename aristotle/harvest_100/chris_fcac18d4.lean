/-
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
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

/-- **Catalan's identity** (addition form, avoiding natural subtraction):
for all `m r : ℕ`,
`fib (m + r) ^ 2 - fib m * fib (m + 2 * r) = (-1) ^ m * fib r ^ 2` in `ℤ`.

This is obtained from the integer-indexed Catalan identity in Mathlib,
`Int.fib_add_sq_sub_fib_mul_fib_add_two_mul`. -/
theorem catalan (m r : ℕ) :
    (Nat.fib (m + r) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2 * r) : ℤ)
      = (-1) ^ m * (Nat.fib r : ℤ) ^ 2 := by
  have h := Int.fib_add_sq_sub_fib_mul_fib_add_two_mul (m : ℤ) (r : ℤ)
  simpa using h

/-- **Catalan's identity**, subtraction form: for `n r : ℕ` with `r ≤ n`,
`fib n ^ 2 - fib (n - r) * fib (n + r) = (-1) ^ (n - r) * fib r ^ 2` in `ℤ`. -/
theorem catalan_sub {n r : ℕ} (h : r ≤ n) :
    (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - r) : ℤ) * (Nat.fib (n + r) : ℤ)
      = (-1) ^ (n - r) * (Nat.fib r : ℤ) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + r := ⟨n - r, by omega⟩
  have hm : m + r - r = m := by omega
  rw [hm]
  have h2 : m + r + r = m + 2 * r := by ring
  rw [h2]
  exact catalan m r

end Fibonacci

