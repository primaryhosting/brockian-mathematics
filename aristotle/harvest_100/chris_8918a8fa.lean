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

/-- Cassini's identity: `F (m+1)^2 - F m * F (m+2) = (-1)^m`. -/
theorem cassini (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2) : ℤ) = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
      have h1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      have h2 : Nat.fib (n + 1 + 2) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
      rw [h2]
      push_cast [h1] at ih ⊢
      linear_combination -ih

/-- Catalan's identity, in addition form (avoiding natural subtraction):
for all `m r : ℕ`, `F (m+r)^2 - F m * F (m + 2r) = (-1)^m * F r ^ 2`. -/
theorem catalan (m r : ℕ) :
    (Nat.fib (m + r) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2 * r) : ℤ)
      = (-1) ^ m * (Nat.fib r : ℤ) ^ 2 := by
  cases r with
  | zero => simp [sq]
  | succ s =>
      have e1 : m + (s + 1) = m + s + 1 := by ring
      have e2 : m + 2 * (s + 1) = m + (2 * s + 1) + 1 := by ring
      have h1 : Nat.fib (m + (s + 1))
          = Nat.fib m * Nat.fib s + Nat.fib (m + 1) * Nat.fib (s + 1) := by
        rw [e1, Nat.fib_add]
      have h2 : Nat.fib (m + 2 * (s + 1))
          = Nat.fib m * Nat.fib (2 * s + 1) + Nat.fib (m + 1) * Nat.fib (2 * s + 1 + 1) := by
        rw [e2, Nat.fib_add]
      have h3 : Nat.fib (2 * s + 1) = Nat.fib (s + 1) ^ 2 + Nat.fib s ^ 2 :=
        Nat.fib_two_mul_add_one s
      have h4 : Nat.fib (2 * s + 1 + 1) = Nat.fib (s + 1) * (2 * Nat.fib s + Nat.fib (s + 1)) := by
        have : 2 * s + 1 + 1 = 2 * s + 2 := by ring
        rw [this, Nat.fib_two_mul_add_two]
      have hc := cassini m
      have hm2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
      rw [h1, h2, h3, h4]
      push_cast [hm2] at hc ⊢
      linear_combination ((Nat.fib (s + 1) : ℤ) ^ 2) * hc

/-- Catalan's identity in the original subtraction form: for `r ≤ n`,
`F n ^ 2 - F (n - r) * F (n + r) = (-1)^(n-r) * F r ^ 2`. -/
theorem catalan_sub (n r : ℕ) (h : r ≤ n) :
    (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - r) : ℤ) * (Nat.fib (n + r) : ℤ)
      = (-1) ^ (n - r) * (Nat.fib r : ℤ) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hm : r + m - r = m := by omega
  have hn : r + m + r = m + 2 * r := by ring
  have hrm : r + m = m + r := by ring
  rw [hm, hn, hrm]
  exact catalan m r

end Fibonacci

