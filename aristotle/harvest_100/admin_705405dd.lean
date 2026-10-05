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

namespace Fibonacci

/-- Cassini's identity: `F(m+1)^2 - F(m) * F(m+2) = (-1)^m`, over `ℤ`. -/
theorem cassini (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2) : ℤ) = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h1 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      simpa using Nat.fib_add_two (n := k + 1)
    have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    have h1' : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h1
    have h2' : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h2
    rw [h2'] at ih
    rw [show k + 1 + 1 = k + 2 from rfl, show k + 1 + 2 = k + 3 from rfl, h1', h2', pow_succ]
    linear_combination -ih

/-- **Catalan's identity** for Fibonacci numbers, in addition form (no `Nat` subtraction):
for all `m r : ℕ`, `F(m+r)^2 - F(m) * F(m+2r) = (-1)^m * F(r)^2`. -/
theorem catalan (m r : ℕ) :
    (Nat.fib (m + r) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2 * r) : ℤ)
      = (-1) ^ m * (Nat.fib r : ℤ) ^ 2 := by
  cases r with
  | zero =>
    simp only [Nat.add_zero, Nat.mul_zero, Nat.fib_zero, Nat.cast_zero]
    ring
  | succ s =>
    -- `F(m+s+1) = F m * F s + F (m+1) * F (s+1)`
    have e1 : Nat.fib (m + (s + 1))
        = Nat.fib m * Nat.fib s + Nat.fib (m + 1) * Nat.fib (s + 1) := by
      have := Nat.fib_add m s
      simpa [Nat.add_assoc] using this
    -- `F(2s+1) = F s * F s + F (s+1) * F (s+1)`
    have e2 : Nat.fib (2 * s + 1) = Nat.fib s * Nat.fib s + Nat.fib (s + 1) * Nat.fib (s + 1) := by
      have := Nat.fib_add s s
      simpa [two_mul] using this
    -- `F(2s+2) = F s * F (s+1) + F (s+1) * F (s+2)`
    have e3 : Nat.fib (2 * s + 2)
        = Nat.fib s * Nat.fib (s + 1) + Nat.fib (s + 1) * Nat.fib (s + 2) := by
      have := Nat.fib_add s (s + 1)
      have h : s + (s + 1) + 1 = 2 * s + 2 := by ring
      rw [h] at this
      exact this
    -- `F(m + 2(s+1)) = F m * F(2s+1) + F(m+1) * F(2s+2)`
    have e4 : Nat.fib (m + 2 * (s + 1))
        = Nat.fib m * Nat.fib (2 * s + 1) + Nat.fib (m + 1) * Nat.fib (2 * s + 2) := by
      have := Nat.fib_add m (2 * s + 1)
      have h : m + (2 * s + 1) + 1 = m + 2 * (s + 1) := by ring
      rw [h] at this
      exact this
    have hs2 : Nat.fib (s + 2) = Nat.fib s + Nat.fib (s + 1) := Nat.fib_add_two
    have hm2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
    have hc := cassini m
    -- move to `ℤ`
    have E1 : (Nat.fib (m + (s + 1)) : ℤ)
        = (Nat.fib m : ℤ) * (Nat.fib s : ℤ) + (Nat.fib (m + 1) : ℤ) * (Nat.fib (s + 1) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) e1
    have E4 : (Nat.fib (m + 2 * (s + 1)) : ℤ)
        = (Nat.fib m : ℤ) * (Nat.fib (2 * s + 1) : ℤ)
          + (Nat.fib (m + 1) : ℤ) * (Nat.fib (2 * s + 2) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) e4
    have E2 : (Nat.fib (2 * s + 1) : ℤ)
        = (Nat.fib s : ℤ) * (Nat.fib s : ℤ) + (Nat.fib (s + 1) : ℤ) * (Nat.fib (s + 1) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) e2
    have E3 : (Nat.fib (2 * s + 2) : ℤ)
        = (Nat.fib s : ℤ) * (Nat.fib (s + 1) : ℤ)
          + (Nat.fib (s + 1) : ℤ) * (Nat.fib (s + 2) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) e3
    have HS2 : (Nat.fib (s + 2) : ℤ) = (Nat.fib s : ℤ) + (Nat.fib (s + 1) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hs2
    have HM2 : (Nat.fib (m + 2) : ℤ) = (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm2
    rw [E1, E4, E2, E3, HS2]
    rw [HM2] at hc
    nlinarith [hc]

/-- **Catalan's identity** in the classical subtraction form: for `r ≤ n`,
`F(n)^2 - F(n-r) * F(n+r) = (-1)^(n-r) * F(r)^2`. -/
theorem catalan_sub (n r : ℕ) (h : r ≤ n) :
    (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - r) : ℤ) * (Nat.fib (n + r) : ℤ)
      = (-1) ^ (n - r) * (Nat.fib r : ℤ) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + r := ⟨n - r, by omega⟩
  have hm : m + r - r = m := by omega
  have hn : m + r + r = m + 2 * r := by ring
  rw [hm, hn]
  exact catalan m r

end Fibonacci

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

