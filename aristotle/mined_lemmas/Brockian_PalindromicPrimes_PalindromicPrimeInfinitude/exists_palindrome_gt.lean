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
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.PalindromicPrimes

/-- A natural number is *palindromic* (in base 10) when its list of base-10 digits
is equal to its own reversal. -/

theorem exists_palindrome_gt (N : ℕ) : ∃ n, N < n ∧ IsPalindrome n := by
  refine ⟨Nat.ofDigits 10 (palList N), ?_, isPalindrome_palNumber N⟩
  set n := Nat.ofDigits 10 (palList N) with hn
  have hd : Nat.digits 10 n = palList N := digits_palNumber N
  have hne : n ≠ 0 := by
    intro h
    have hnil : Nat.digits 10 n = [] := by rw [h]; simp
    rw [hd] at hnil
    simp [palList] at hnil
  have hle : (10 : ℕ) ^ (Nat.digits 10 n).length ≤ 10 * n :=
    Nat.base_pow_length_digits_le 10 n (by norm_num) hne
  rw [hd, palList_length] at hle
  have h1 : (10 : ℕ) ^ (N + 2) = 10 * 10 ^ (N + 1) := by ring
  have h2 : N < 10 ^ N := Nat.lt_pow_self (by norm_num)
  have h3 : (10:ℕ) ^ N ≤ 10 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ## The conditional reduction

The infinitude of palindromic primes is an open problem: no unconditional proof is
known.  What is proved here is the reduction of the infinitude statement to the (still
open) statement that there exist palindromic primes with arbitrarily many base-10
digits. -/

/-- **Conditional infinitude of palindromic primes.**  If for every `k` there is a
palindromic prime with more than `k` base-10 digits, then there are infinitely many
palindromic primes. -/
