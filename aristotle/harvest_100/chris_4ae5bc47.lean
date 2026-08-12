/-
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
Verification: pending
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

/-- Cassini's identity: `fib (m+1)^2 - fib m * fib (m+2) = (-1)^m`. -/
theorem cassini (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2) : ℤ) = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      have h1 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      have h2 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
      have h1' : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) h1
      have h2' : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) h2
      have hidx1 : (k + 1) + 1 = k + 2 := rfl
      have hidx2 : (k + 1) + 2 = k + 3 := rfl
      rw [hidx1, hidx2, h2', h1']
      have hpow : ((-1 : ℤ)) ^ (k + 1) = -((-1 : ℤ) ^ k) := by rw [pow_succ]; ring
      have ih' : (Nat.fib (k + 1) : ℤ) ^ 2
          - (Nat.fib k : ℤ) * ((Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ)) = (-1) ^ k := by
        rw [← h1']; exact ih
      rw [hpow]
      linear_combination -ih'

/-- Catalan's identity, in addition form (no natural subtraction):
`fib (m+r)^2 - fib m * fib (m+2r) = (-1)^m * fib r ^ 2`. -/
theorem catalan (m r : ℕ) :
    (Nat.fib (m + r) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2 * r) : ℤ)
      = (-1) ^ m * (Nat.fib r : ℤ) ^ 2 := by
  cases r with
  | zero =>
      have hm : m + 2 * 0 = m := by omega
      rw [hm]
      simp [sq]
  | succ s =>
      -- abbreviations
      set A : ℤ := (Nat.fib m : ℤ) with hA
      set B : ℤ := (Nat.fib (m + 1) : ℤ) with hB
      set p : ℤ := (Nat.fib s : ℤ) with hp
      set q : ℤ := (Nat.fib (s + 1) : ℤ) with hq
      -- fib (m + s + 1) = fib m * fib s + fib (m+1) * fib (s+1)
      have e1 : (Nat.fib (m + (s + 1)) : ℤ) = A * p + B * q := by
        have h : (Nat.fib (m + s + 1) : ℤ)
            = (Nat.fib m : ℤ) * (Nat.fib s : ℤ)
              + (Nat.fib (m + 1) : ℤ) * (Nat.fib (s + 1) : ℤ) := by
          exact_mod_cast Nat.fib_add m s
        simpa [hA, hB, hp, hq, Nat.add_assoc] using h
      -- fib (2s+1) = fib s ^ 2 + fib (s+1) ^ 2
      have e2 : (Nat.fib (s + s + 1) : ℤ) = p ^ 2 + q ^ 2 := by
        have h : (Nat.fib (s + s + 1) : ℤ)
            = (Nat.fib s : ℤ) * (Nat.fib s : ℤ)
              + (Nat.fib (s + 1) : ℤ) * (Nat.fib (s + 1) : ℤ) := by
          exact_mod_cast Nat.fib_add s s
        rw [h]; ring
      -- fib (2s+2) = 2 * fib s * fib (s+1) + fib (s+1)^2
      have e3 : (Nat.fib (s + s + 2) : ℤ) = 2 * p * q + q ^ 2 := by
        have h := Nat.fib_add (s + 1) s
        have h' : (Nat.fib (s + 1 + s + 1) : ℤ)
            = (Nat.fib (s + 1) : ℤ) * (Nat.fib s : ℤ)
              + (Nat.fib (s + 1 + 1) : ℤ) * (Nat.fib (s + 1) : ℤ) := by exact_mod_cast h
        have hidx : s + 1 + s + 1 = s + s + 2 := by omega
        have h2 : (Nat.fib (s + 2) : ℤ) = p + q := by
          have hf : (Nat.fib (s + 2) : ℤ) = (Nat.fib s : ℤ) + (Nat.fib (s + 1) : ℤ) := by
            exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (Nat.fib_add_two (n := s))
          simpa [hp, hq] using hf
        rw [hidx] at h'
        have hs1 : s + 1 + 1 = s + 2 := rfl
        rw [hs1, h2] at h'
        rw [h']; ring
      -- fib (m + 2(s+1)) = fib m * fib (2s+1) + fib (m+1) * fib (2s+2)
      have e4 : (Nat.fib (m + 2 * (s + 1)) : ℤ)
          = A * (p ^ 2 + q ^ 2) + B * (2 * p * q + q ^ 2) := by
        have h := Nat.fib_add m (s + s + 1)
        have h' : (Nat.fib (m + (s + s + 1) + 1) : ℤ)
            = (Nat.fib m : ℤ) * (Nat.fib (s + s + 1) : ℤ)
              + (Nat.fib (m + 1) : ℤ) * (Nat.fib (s + s + 1 + 1) : ℤ) := by exact_mod_cast h
        have hidx : m + (s + s + 1) + 1 = m + 2 * (s + 1) := by ring
        have hidx2 : s + s + 1 + 1 = s + s + 2 := by omega
        rw [hidx, hidx2, e2, e3] at h'
        rw [h']
      -- Cassini
      have hcas : B ^ 2 - A * (A + B) = (-1) ^ m := by
        have hc := cassini m
        have hfib : (Nat.fib (m + 2) : ℤ) = A + B := by
          have hf : (Nat.fib (m + 2) : ℤ) = (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ) := by
            exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (Nat.fib_add_two (n := m))
          simpa [hA, hB] using hf
        rw [hfib] at hc
        simpa [hA, hB] using hc
      rw [e1, e4]
      have hring : (A * p + B * q) ^ 2 - A * (A * (p ^ 2 + q ^ 2) + B * (2 * p * q + q ^ 2))
          = (B ^ 2 - A * (A + B)) * q ^ 2 := by ring
      rw [hring, hcas]

/-- Catalan's identity in the original subtraction form, for `r ≤ n`. -/
theorem catalan_sub (n r : ℕ) (h : r ≤ n) :
    (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - r) : ℤ) * (Nat.fib (n + r) : ℤ)
      = (-1) ^ (n - r) * (Nat.fib r : ℤ) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : r + m - r = m := by omega
  have h2 : r + m + r = m + 2 * r := by omega
  rw [h1, h2, Nat.add_comm r m]
  exact catalan m r

end Fibonacci

