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

namespace Brockian

/-- The two-prime ("K2") Goldbach wheel condition at modulus `m`.

Thinking of the residues mod `m` as a wheel, this says that the wheel is *fully covered*
by sums of two prime spokes: every residue class `n` mod `m` can be hit by a sum `p + q`
of two primes, both coprime to `m` (i.e. both lying on the wheel), and with the two primes
taken arbitrarily large.  This is the exact local-at-`m` statement underlying a Goldbach-type
two-prime representation: no residue class mod `m` is obstructed. -/

theorem exists_add_mod_eq_of_three_le {P : ℕ} (hP : 3 ≤ P) (n : ℕ) :
    ∃ a b : ℕ, 0 < a ∧ a < P ∧ 0 < b ∧ b < P ∧ (a + b) % P = n % P := by
  have hPpos : 0 < P := by omega
  have hr : n % P < P := Nat.mod_lt _ hPpos
  rcases eq_or_ne (n % P) 0 with h0 | h0
  · refine ⟨1, P - 1, by omega, by omega, by omega, by omega, ?_⟩
    have h1 : 1 + (P - 1) = P := by omega
    rw [h1, Nat.mod_self, h0]
  rcases eq_or_ne (n % P) 1 with h1 | h1
  · refine ⟨2, P - 1, by omega, by omega, by omega, by omega, ?_⟩
    have h2 : 2 + (P - 1) = P + 1 := by omega
    rw [h2, h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  · refine ⟨1, n % P - 1, by omega, by omega, by omega, by omega, ?_⟩
    have h3 : 1 + (n % P - 1) = n % P := by omega
    rw [h3]
    exact Nat.mod_eq_of_lt hr

/-- A residue strictly between `0` and a prime `P` is coprime to `P`. -/
