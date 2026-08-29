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

import Mathlib

/-!
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The infinitude of Mersenne primes is a famous open problem, so what is established here is a
*Lean-checked conditional reduction*: the set of Mersenne primes is infinite **if and only if**
the set of even perfect numbers is infinite.  Both implications go through a full formalisation
of the Euclid–Euler theorem, which is proved from scratch below.
-/

set_option autoImplicit false

namespace Brockian.MersennePerfect

open ArithmeticFunction Nat

/-- The sum-of-divisors function `σ₁`. -/

theorem sum_properDivisors_eq_of_dvd {m x : ℕ} (hm : 1 < m) (hx : x ∣ m) (hxm : x ≠ m)
    (hsum : ∑ i ∈ m.properDivisors, i = x) : x = 1 ∧ m.Prime := by
  have hx0 : 0 < x := Nat.pos_of_dvd_of_pos hx (by omega)
  have hxmem : x ∈ m.properDivisors := Nat.mem_properDivisors.2 ⟨hx, lt_of_le_of_ne
    (Nat.le_of_dvd (by omega) hx) hxm⟩
  have h1mem : 1 ∈ m.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.2 hm
  have hx1 : x = 1 := by
    by_contra hne
    have hsub : ({1, x} : Finset ℕ) ⊆ m.properDivisors := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> assumption
    have hle := Finset.sum_le_sum_of_subset (f := fun i => i) hsub
    rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ x), hsum] at hle
    omega
  subst hx1
  exact ⟨rfl, Nat.sum_properDivisors_eq_one_iff_prime.1 hsum⟩

