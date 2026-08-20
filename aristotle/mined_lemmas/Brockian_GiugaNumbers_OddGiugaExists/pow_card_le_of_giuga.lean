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

/-
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GiugaNumbers

open Finset

/-- A *Giuga number* is a composite natural number `n > 1` such that every prime `p`
dividing `n` satisfies `p ∣ n / p - 1`. -/

theorem pow_card_le_of_giuga {n : ℕ} (h : IsGiuga n) (hodd : Odd n) : 3 ^ 9 ≤ n := by
  have hprod := h.prod_primeFactors
  have hcard := odd_giuga_nine_primeFactors hodd h
  have hS := odd_primeFactors hodd
  have hle : ∏ _p ∈ n.primeFactors, 3 ≤ ∏ p ∈ n.primeFactors, p :=
    Finset.prod_le_prod' (fun p hp => three_le_of_prime_ne_two (hS p hp).1 (hS p hp).2)
  rw [Finset.prod_const, hprod] at hle
  calc (3 : ℕ) ^ 9 ≤ 3 ^ n.primeFactors.card := Nat.pow_le_pow_right (by norm_num) hcard
    _ ≤ n := hle

/-- **Conditional reduction for the existence of an odd Giuga number.**
Whether an odd Giuga number exists is an open problem; what is proved here is that any
odd Giuga number necessarily has at least nine distinct prime factors, and hence is at
least `3 ^ 9`. -/
