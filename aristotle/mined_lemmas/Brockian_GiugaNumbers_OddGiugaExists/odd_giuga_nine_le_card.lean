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
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.GiugaNumbers

/-- A *Giuga number* is a composite natural number `n > 1` such that
`p ∣ n / p - 1` for every prime `p` dividing `n`. -/

theorem odd_giuga_nine_le_card {n : ℕ} (hodd : Odd n) (h : IsGiuga n) :
    9 ≤ n.primeFactors.card := by
  by_contra hlt
  push_neg at hlt
  have hcard : n.primeFactors.card ≤ 8 := by omega
  have hp : ∀ p ∈ n.primeFactors, p.Prime := fun p hpm => Nat.prime_of_mem_primeFactors hpm
  have h2 : ∀ p ∈ n.primeFactors, p ≠ 2 := by
    intro p hpm hp2
    subst hp2
    have hd : (2 : ℕ) ∣ n := Nat.dvd_of_mem_primeFactors hpm
    rw [Nat.odd_iff] at hodd
    omega
  exact absurd h.one_lt_sum_inv (not_lt.2 (sum_inv_lt_one_of_odd_primes hp h2 hcard).le)

/-- An odd Giuga number is at least `3 ^ 9 = 19683`, since it is a product of at least nine
distinct odd primes. -/
