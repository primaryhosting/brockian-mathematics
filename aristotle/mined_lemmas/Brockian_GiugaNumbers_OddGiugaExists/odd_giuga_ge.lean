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

theorem odd_giuga_ge {n : ℕ} (hodd : Odd n) (h : IsGiuga n) : 19683 ≤ n := by
  have hcard : 9 ≤ n.primeFactors.card := odd_giuga_nine_le_card hodd h
  have hprod : ∏ p ∈ n.primeFactors, p = n := h.prod_primeFactors
  have hge : ∀ p ∈ n.primeFactors, 3 ≤ p := by
    intro p hpm
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have hp2 : p ≠ 2 := by
      intro hp2
      subst hp2
      have hd : (2 : ℕ) ∣ n := Nat.dvd_of_mem_primeFactors hpm
      rw [Nat.odd_iff] at hodd
      omega
    have := hpp.two_le
    omega
  have hpow : 3 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    calc 3 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 3 := by
          rw [Finset.prod_const]
      _ ≤ ∏ p ∈ n.primeFactors, p := Finset.prod_le_prod' hge
  have h39 : (3 : ℕ) ^ 9 ≤ 3 ^ n.primeFactors.card := Nat.pow_le_pow_right (by norm_num) hcard
  calc (19683 : ℕ) = 3 ^ 9 := by norm_num
    _ ≤ 3 ^ n.primeFactors.card := h39
    _ ≤ ∏ p ∈ n.primeFactors, p := hpow
    _ = n := hprod

/-- **Conditional existence of an odd Giuga number.**

Whether an odd Giuga number exists is an open problem.  This is a Lean-checked reduction:
if there is a finite set `S` of at least two odd primes such that every `p ∈ S`
divides `(∏ q ∈ S.erase p, q) - 1`, then `∏ p ∈ S, p` is an odd Giuga number, so an odd
Giuga number exists. -/
