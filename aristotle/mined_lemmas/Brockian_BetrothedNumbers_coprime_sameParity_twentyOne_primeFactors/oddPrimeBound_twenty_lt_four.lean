import Mathlib
/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- A *betrothed* (quasi-amicable) pair: two positive integers, each of whose
divisor sums equals the sum of the pair plus one. -/

lemma oddPrimeBound_twenty_lt_four : oddPrimeBound 20 < 4 := by
  have e1 : Nat.nth Nat.Prime 1 = 3 := nth_prime_eq (by norm_num) (by decide)
  have e2 : Nat.nth Nat.Prime 2 = 5 := nth_prime_eq (by norm_num) (by decide)
  have e3 : Nat.nth Nat.Prime 3 = 7 := nth_prime_eq (by norm_num) (by decide)
  have e4 : Nat.nth Nat.Prime 4 = 11 := nth_prime_eq (by norm_num) (by decide)
  have e5 : Nat.nth Nat.Prime 5 = 13 := nth_prime_eq (by norm_num) (by decide)
  have e6 : Nat.nth Nat.Prime 6 = 17 := nth_prime_eq (by norm_num) (by decide)
  have e7 : Nat.nth Nat.Prime 7 = 19 := nth_prime_eq (by norm_num) (by decide)
  have e8 : Nat.nth Nat.Prime 8 = 23 := nth_prime_eq (by norm_num) (by decide)
  have e9 : Nat.nth Nat.Prime 9 = 29 := nth_prime_eq (by norm_num) (by decide)
  have e10 : Nat.nth Nat.Prime 10 = 31 := nth_prime_eq (by norm_num) (by decide)
  have e11 : Nat.nth Nat.Prime 11 = 37 := nth_prime_eq (by norm_num) (by decide)
  have e12 : Nat.nth Nat.Prime 12 = 41 := nth_prime_eq (by norm_num) (by decide)
  have e13 : Nat.nth Nat.Prime 13 = 43 := nth_prime_eq (by norm_num) (by decide)
  have e14 : Nat.nth Nat.Prime 14 = 47 := nth_prime_eq (by norm_num) (by decide)
  have e15 : Nat.nth Nat.Prime 15 = 53 := nth_prime_eq (by norm_num) (by decide)
  have e16 : Nat.nth Nat.Prime 16 = 59 := nth_prime_eq (by norm_num) (by decide)
  have e17 : Nat.nth Nat.Prime 17 = 61 := nth_prime_eq (by norm_num) (by decide)
  have e18 : Nat.nth Nat.Prime 18 = 67 := nth_prime_eq (by norm_num) (by decide)
  have e19 : Nat.nth Nat.Prime 19 = 71 := nth_prime_eq (by norm_num) (by decide)
  have e20 : Nat.nth Nat.Prime 20 = 73 := nth_prime_eq (by norm_num) (by decide)
  rw [oddPrimeBound]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero,
    show (0:ℕ) + 1 = 1 from rfl, show (1:ℕ) + 1 = 2 from rfl, show (2:ℕ) + 1 = 3 from rfl,
    show (3:ℕ) + 1 = 4 from rfl, show (4:ℕ) + 1 = 5 from rfl, show (5:ℕ) + 1 = 6 from rfl,
    show (6:ℕ) + 1 = 7 from rfl, show (7:ℕ) + 1 = 8 from rfl, show (8:ℕ) + 1 = 9 from rfl,
    show (9:ℕ) + 1 = 10 from rfl, show (10:ℕ) + 1 = 11 from rfl, show (11:ℕ) + 1 = 12 from rfl,
    show (12:ℕ) + 1 = 13 from rfl, show (13:ℕ) + 1 = 14 from rfl, show (14:ℕ) + 1 = 15 from rfl,
    show (15:ℕ) + 1 = 16 from rfl, show (16:ℕ) + 1 = 17 from rfl, show (17:ℕ) + 1 = 18 from rfl,
    show (18:ℕ) + 1 = 19 from rfl, show (19:ℕ) + 1 = 20 from rfl,
    e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20,
    abFactor]
  norm_num

