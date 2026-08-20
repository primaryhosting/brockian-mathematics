/-!
# D Ocagne
Category: Fibonacci
Target: Fibonacci.dOcagne
Statement: d'Ocagne's identity: for all m n : Nat, (Nat.fib m : Int) * (Nat.fib (n+1)) - (Nat.fib (m+1)) * (Nat.fib n) = (-1)^n * (Nat.fib (m - n)) for m >= n. State the addition form to avoid subtraction: for all m n : Nat, (Nat.fib (m+n+1) : Int) = Nat.fib (m+1)*Nat.fib (n+1) + Nat.fib m * Nat.fib n.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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
theorem dOcagne_shifted (n d : ℕ) :
    (Nat.fib (n + d) : ℤ) * Nat.fib (n + 1) - (Nat.fib (n + d + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib d := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : Nat.fib (n + 1 + 1) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      have h2 : Nat.fib (n + d + 1 + 1) = Nat.fib (n + d) + Nat.fib (n + d + 1) :=
        Nat.fib_add_two
      have h3 : n + 1 + d = n + d + 1 := by omega
      rw [h3, h1, h2, pow_succ]
      push_cast
      nlinarith [ih]

/-- **d'Ocagne's identity**, subtraction form: for `n ≤ m`,
`F m * F (n+1) - F (m+1) * F n = (-1)^n * F (m - n)`. -/
theorem dOcagne_sub {m n : ℕ} (h : n ≤ m) :
    (Nat.fib m : ℤ) * Nat.fib (n + 1) - (Nat.fib (m + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib (m - n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using dOcagne_shifted n d

end Fibonacci

