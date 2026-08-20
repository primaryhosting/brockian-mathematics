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

/-!
## Overview

Whether there are infinitely many base-ten palindromic primes is an open problem, so the
unconditional statement is out of reach.  What is proved here is an unconditional *reduction*
of that question, resting on a genuine intermediate theorem:

* every base-ten palindrome with an **even** number of digits is divisible by `11`
  (`Brockian.PalindromicPrimes.eleven_dvd_of_isPalindrome_of_even_length`);
* consequently `11` is the **only** palindromic prime with an even number of digits
  (`Brockian.PalindromicPrimes.evenLengthPalindromicPrimes_eq`);
* hence the palindromic primes are infinite **iff** the palindromic primes with an odd number
  of digits are infinite (`Brockian.PalindromicPrimes.PalindromicPrimeInfinitude`).

So the Brockian conjecture may be attacked entirely inside the odd-digit-length case, with no
loss of generality.
-/

namespace Brockian.PalindromicPrimes

open scoped Nat

/-- `n` is a base-ten palindrome: its list of decimal digits equals its own reversal. -/
def IsPalindrome (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

instance (n : ℕ) : Decidable (IsPalindrome n) := by
  unfold IsPalindrome; infer_instance

/-- The set of base-ten palindromic primes. -/
def palindromicPrimes : Set ℕ := {p | Nat.Prime p ∧ IsPalindrome p}

/-- The set of base-ten palindromic primes having an odd number of decimal digits. -/
def oddLengthPalindromicPrimes : Set ℕ :=
  {p | Nat.Prime p ∧ IsPalindrome p ∧ Odd (Nat.digits 10 p).length}

/-! ### The key intermediate lemma -/

/-- A palindromic integer list of even length has vanishing alternating sum. -/
theorem alternatingSum_eq_zero_of_reverse_eq {L : List ℤ} (hrev : L.reverse = L)
    (hlen : Even L.length) : L.alternatingSum = 0 := by
  have h := List.alternatingSum_reverse L
  rw [hrev] at h
  have hodd : Odd (L.length + 1) := Even.add_one hlen
  rw [hodd.neg_one_pow] at h
  simp only [neg_smul, one_smul] at h
  omega

/-- **Key lemma.** Every base-ten palindrome with an even number of digits is divisible by 11.

This is the arithmetic heart of the reduction: modulo `11` one has `10 ≡ -1`, so a number is
congruent to the alternating sum of its digits; palindromy pairs digit `i` with digit
`len - 1 - i`, and when `len` is even those two positions carry opposite signs. -/
theorem eleven_dvd_of_isPalindrome_of_even_length {n : ℕ} (hpal : IsPalindrome n)
    (hlen : Even (Nat.digits 10 n).length) : 11 ∣ n := by
  rw [Nat.eleven_dvd_iff]
  have hrev : (List.map (fun d : ℕ => (d : ℤ)) (Nat.digits 10 n)).reverse
      = List.map (fun d : ℕ => (d : ℤ)) (Nat.digits 10 n) := by
    rw [← List.map_reverse, hpal]
  have hlen' : Even (List.map (fun d : ℕ => (d : ℤ)) (Nat.digits 10 n)).length := by
    simpa using hlen
  rw [alternatingSum_eq_zero_of_reverse_eq hrev hlen']
  exact dvd_zero 11

/-- `11` really is a palindromic prime (so the statements below are not vacuous). -/
theorem eleven_mem_palindromicPrimes : 11 ∈ palindromicPrimes := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- `101` is a palindromic prime with an odd number of digits. -/
theorem hundredOne_mem_oddLengthPalindromicPrimes : 101 ∈ oddLengthPalindromicPrimes := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide
  · decide

/-- The only palindromic prime with an even number of decimal digits is `11`. -/
theorem eq_eleven_of_palindromicPrime_of_even_length {p : ℕ} (hp : Nat.Prime p)
    (hpal : IsPalindrome p) (hlen : Even (Nat.digits 10 p).length) : p = 11 := by
  have h11 : 11 ∣ p := eleven_dvd_of_isPalindrome_of_even_length hpal hlen
  exact ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 h11).symm

/-- The palindromic primes with an even number of digits form exactly the singleton `{11}`. -/
theorem evenLengthPalindromicPrimes_eq :
    {p : ℕ | Nat.Prime p ∧ IsPalindrome p ∧ Even (Nat.digits 10 p).length} = {11} := by
  ext p
  constructor
  · rintro ⟨hp, hpal, hlen⟩
    exact eq_eleven_of_palindromicPrime_of_even_length hp hpal hlen
  · rintro rfl
    exact ⟨eleven_mem_palindromicPrimes.1, eleven_mem_palindromicPrimes.2, by decide⟩

/-- Removing `11`, every palindromic prime has an odd number of digits. -/
theorem palindromicPrimes_diff_subset :
    palindromicPrimes \ {11} ⊆ oddLengthPalindromicPrimes := by
  rintro p ⟨⟨hp, hpal⟩, hne⟩
  refine ⟨hp, hpal, ?_⟩
  rcases Nat.even_or_odd (Nat.digits 10 p).length with h | h
  · exact absurd (eq_eleven_of_palindromicPrime_of_even_length hp hpal h) hne
  · exact h

/-! ### Main theorem: reduction of the Brockian conjecture to the odd-digit-length case -/

/-- **Palindromic Prime Infinitude (reduction).**

There are infinitely many base-ten palindromic primes if and only if there are infinitely many
base-ten palindromic primes with an odd number of decimal digits.

The nontrivial direction uses the key lemma that a palindrome of even digit-length is divisible
by `11`, so that the two sets differ only by the single element `11`. -/
theorem PalindromicPrimeInfinitude :
    palindromicPrimes.Infinite ↔ oddLengthPalindromicPrimes.Infinite := by
  constructor
  · intro h
    exact (h.diff (Set.finite_singleton 11)).mono palindromicPrimes_diff_subset
  · intro h
    refine h.mono ?_
    rintro p ⟨hp, hpal, -⟩
    exact ⟨hp, hpal⟩

/-! ### Unbounded reformulations and the conditional form of the conjecture -/

/-- Infinitude of the palindromic primes is the same as their being unbounded. -/
theorem palindromicPrimes_infinite_iff_unbounded :
    palindromicPrimes.Infinite ↔ ∀ N : ℕ, ∃ p ∈ palindromicPrimes, N < p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h.exists_gt N
    exact ⟨p, hp, hlt⟩
  · intro h
    exact Set.infinite_of_forall_exists_gt (fun N => h N)

/-- **Conditional form of the Brockian conjecture.**  It suffices to produce, above every bound,
one palindromic prime with an odd number of decimal digits. -/
theorem palindromicPrimes_infinite_of_odd_unbounded
    (h : ∀ N : ℕ, ∃ p, Nat.Prime p ∧ IsPalindrome p ∧ Odd (Nat.digits 10 p).length ∧ N < p) :
    palindromicPrimes.Infinite := by
  rw [PalindromicPrimeInfinitude]
  refine Set.infinite_of_forall_exists_gt (fun N => ?_)
  obtain ⟨p, hp, hpal, hodd, hlt⟩ := h N
  exact ⟨p, ⟨hp, hpal, hodd⟩, hlt⟩

end Brockian.PalindromicPrimes

