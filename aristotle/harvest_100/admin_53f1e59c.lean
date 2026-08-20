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

/-- Cassini's identity, stated over the integers. -/
theorem cassini (n : Nat) :
    (Nat.fib (n + 2) : Int) * (Nat.fib n) - (Nat.fib (n + 1)) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hf : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have hf2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    push_cast [hf, hf2] at ih ⊢
    ring_nf
    ring_nf at ih
    linarith [ih, pow_succ (-1 : Int) (k + 1)]

/-- Cassini's identity for even `n`, stated over the natural numbers. -/
theorem cassini_even {n : Nat} (hn : Even n) :
    Nat.fib (n + 2) * Nat.fib n + 1 = Nat.fib (n + 1) ^ 2 := by
  have h := cassini n
  have hpow : ((-1 : Int)) ^ (n + 1) = -1 := by
    rcases hn with ⟨m, hm⟩
    subst hm
    rw [show m + m + 1 = 2 * m + 1 by ring, pow_succ, pow_mul]
    norm_num
  rw [hpow] at h
  have : ((Nat.fib (n + 2) * Nat.fib n + 1 : Nat) : Int) = ((Nat.fib (n + 1) ^ 2 : Nat) : Int) := by
    push_cast
    linarith
  exact_mod_cast this

/-- Cassini's identity for odd `n`, stated over the natural numbers. -/
theorem cassini_odd {n : Nat} (hn : Odd n) :
    Nat.fib (n + 1) ^ 2 + 1 = Nat.fib (n + 2) * Nat.fib n := by
  have h := cassini n
  have hpow : ((-1 : Int)) ^ (n + 1) = 1 := by
    rcases hn with ⟨m, hm⟩
    subst hm
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]
    norm_num
  rw [hpow] at h
  have : ((Nat.fib (n + 1) ^ 2 + 1 : Nat) : Int) = ((Nat.fib (n + 2) * Nat.fib n : Nat) : Int) := by
    push_cast
    linarith
  exact_mod_cast this

end Fibonacci

