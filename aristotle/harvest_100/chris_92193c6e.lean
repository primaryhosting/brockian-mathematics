import Mathlib

/-!
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Fibonacci

/-- Cassini's identity: `F (m+1) ^ 2 - F m * F (m+2) = (-1)^m` over `ℤ`. -/
theorem cassini (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2) : ℤ) = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      have h2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        exact_mod_cast Nat.fib_add_two (n := k)
      have h3 : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        exact_mod_cast Nat.fib_add_two (n := k + 1)
      have hg : k + 1 + 2 = k + 3 := rfl
      have hg' : k + 1 + 1 = k + 2 := rfl
      rw [hg, hg', h3, pow_succ]
      linear_combination (Nat.fib (k + 2) : ℤ) * h2 - ih

/-- d'Ocagne's identity: `F (m+r) * F (m+1) - F m * F (m+r+1) = (-1)^m * F r`. -/
theorem dOcagne (m r : ℕ) :
    (Nat.fib (m + r) : ℤ) * (Nat.fib (m + 1) : ℤ)
      - (Nat.fib m : ℤ) * (Nat.fib (m + r + 1) : ℤ) = (-1) ^ m * (Nat.fib r : ℤ) := by
  cases r with
  | zero => simp
  | succ s =>
      have e1 : (Nat.fib (m + s + 1) : ℤ)
          = (Nat.fib m : ℤ) * (Nat.fib s : ℤ) + (Nat.fib (m + 1) : ℤ) * (Nat.fib (s + 1) : ℤ) := by
        exact_mod_cast Nat.fib_add m s
      have e2 : (Nat.fib (m + s + 2) : ℤ)
          = (Nat.fib m : ℤ) * (Nat.fib (s + 1) : ℤ)
            + (Nat.fib (m + 1) : ℤ) * (Nat.fib (s + 2) : ℤ) := by
        exact_mod_cast Nat.fib_add m (s + 1)
      have e3 : (Nat.fib (s + 2) : ℤ) = (Nat.fib s : ℤ) + (Nat.fib (s + 1) : ℤ) := by
        exact_mod_cast Nat.fib_add_two (n := s)
      have e4 : (Nat.fib (m + 2) : ℤ) = (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ) := by
        exact_mod_cast Nat.fib_add_two (n := m)
      have hc : (Nat.fib (m + 1) : ℤ) ^ 2 - (Nat.fib m : ℤ) ^ 2
          - (Nat.fib m : ℤ) * (Nat.fib (m + 1) : ℤ) = (-1) ^ m := by
        have h := cassini m
        rw [e4] at h
        linear_combination h
      have hm : m + (s + 1) = m + s + 1 := by omega
      have hm2 : m + s + 1 + 1 = m + s + 2 := by omega
      rw [hm, hm2, e1, e2, e3]
      linear_combination (Nat.fib (s + 1) : ℤ) * hc

/-- Catalan's identity, addition form (avoiding natural subtraction):
`F (m+r) ^ 2 - F m * F (m + 2*r) = (-1)^m * F r ^ 2`. -/
theorem catalan_add (m r : ℕ) :
    (Nat.fib (m + r) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2 * r) : ℤ)
      = (-1) ^ m * (Nat.fib r : ℤ) ^ 2 := by
  cases r with
  | zero => simp [pow_two]
  | succ s =>
      have e1 : (Nat.fib (m + s + 1) : ℤ)
          = (Nat.fib m : ℤ) * (Nat.fib s : ℤ) + (Nat.fib (m + 1) : ℤ) * (Nat.fib (s + 1) : ℤ) := by
        exact_mod_cast Nat.fib_add m s
      have e2 : (Nat.fib (m + s + 1 + s + 1) : ℤ)
          = (Nat.fib (m + s + 1) : ℤ) * (Nat.fib s : ℤ)
            + (Nat.fib (m + s + 2) : ℤ) * (Nat.fib (s + 1) : ℤ) := by
        exact_mod_cast Nat.fib_add (m + s + 1) s
      have hd := dOcagne m (s + 1)
      have hm : m + (s + 1) = m + s + 1 := by omega
      have hm2 : m + s + 1 + 1 = m + s + 2 := by omega
      rw [hm, hm2] at hd
      rw [hm, show m + 2 * (s + 1) = m + s + 1 + s + 1 by omega, e2]
      linear_combination (Nat.fib (s + 1) : ℤ) * hd + (Nat.fib (m + s + 1) : ℤ) * e1

/-- **Catalan's identity** (a generalisation of Cassini's identity): for `r ≤ n`,
`F n ^ 2 - F (n - r) * F (n + r) = (-1)^(n-r) * F r ^ 2`. -/
theorem catalan (n r : ℕ) (h : r ≤ n) :
    (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - r) : ℤ) * (Nat.fib (n + r) : ℤ)
      = (-1) ^ (n - r) * (Nat.fib r : ℤ) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [show r + m - r = m by omega, show r + m + r = m + 2 * r by omega,
    show r + m = m + r by omega]
  exact catalan_add m r

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

