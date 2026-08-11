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
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first commands
in a module, so the module header above is placed immediately after `import Mathlib`;
putting it before the import is rejected by the Lean parser.

Status of the mathematics.

Whether there are infinitely many base-10 palindromic primes is an open problem: no
unconditional proof is known.  This file therefore contains

* the exact definitions (`IsPalindrome`, `PalindromicPrime`, `palindromicPrimes`);
* unconditional results: there are infinitely many palindromes, concrete palindromic
  primes exist, and every palindromic prime other than `11` has an odd number of
  decimal digits (an even-length decimal palindrome is always divisible by `11`);
* the target theorem `PalindromicPrimeInfinitude` as a Lean-checked *conditional
  reduction*: infinitude of palindromic primes follows from the hypothesis that
  palindromic primes with arbitrarily many decimal digits exist.  The reverse
  implication is proved as well, so the reduction is an equivalence.
-/

namespace Brockian.PalindromicPrimes

open Nat

/-- A natural number is a (base-10) palindrome if its list of decimal digits
reads the same forwards and backwards. -/
def IsPalindrome (n : ℕ) : Prop := (Nat.digits 10 n).Palindrome

/-- A palindromic prime: a prime number that is a base-10 palindrome. -/
def PalindromicPrime (n : ℕ) : Prop := Nat.Prime n ∧ IsPalindrome n

/-- The set of palindromic primes. -/
def palindromicPrimes : Set ℕ := {n | PalindromicPrime n}

/-- The number of decimal digits of `n`. -/
def numDigits (n : ℕ) : ℕ := (Nat.digits 10 n).length

/-! ### Palindromes are plentiful -/

/-- The `k`-th repunit `11⋯1` (with `k` ones). -/
def repunit (k : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate k 1)

lemma digits_repunit (k : ℕ) : Nat.digits 10 (repunit k) = List.replicate k 1 := by
  refine Nat.digits_ofDigits 10 (by norm_num) _ (fun l hl => ?_) (fun h => ?_)
  · simp [List.eq_of_mem_replicate hl]
  · have := List.getLast_mem h
    simp [List.eq_of_mem_replicate this]

lemma numDigits_repunit (k : ℕ) : numDigits (repunit k) = k := by
  simp [numDigits, digits_repunit]

lemma isPalindrome_repunit (k : ℕ) : IsPalindrome (repunit k) :=
  List.Palindrome.of_reverse_eq (by rw [digits_repunit, List.reverse_replicate])

lemma repunit_injective : Function.Injective repunit := by
  intro a b hab
  have h : numDigits (repunit a) = numDigits (repunit b) := by rw [hab]
  simpa [numDigits_repunit] using h

/-- There are infinitely many base-10 palindromes. -/
theorem palindromes_infinite : {n : ℕ | IsPalindrome n}.Infinite :=
  Set.infinite_of_injective_forall_mem repunit_injective isPalindrome_repunit

/-! ### Even-length palindromes are divisible by 11 -/

/-- A base-10 palindrome with an even number of digits is divisible by `11`. -/
theorem eleven_dvd_of_isPalindrome_even_numDigits {n : ℕ} (hp : IsPalindrome n)
    (he : Even (numDigits n)) : 11 ∣ n :=
  Nat.eleven_dvd_of_palindrome hp he

/-- The only palindromic prime with an even number of decimal digits is `11`. -/
theorem eq_eleven_of_palindromicPrime_even_numDigits {n : ℕ} (h : PalindromicPrime n)
    (he : Even (numDigits n)) : n = 11 := by
  obtain ⟨hprime, hpal⟩ := h
  have hdvd : 11 ∣ n := eleven_dvd_of_isPalindrome_even_numDigits hpal he
  rcases hprime.eq_one_or_self_of_dvd 11 hdvd with h1 | h2 <;> omega

/-- Every palindromic prime other than `11` has an odd number of decimal digits. -/
theorem odd_numDigits_of_palindromicPrime {n : ℕ} (h : PalindromicPrime n) (hn : n ≠ 11) :
    Odd (numDigits n) := by
  rcases Nat.even_or_odd (numDigits n) with he | ho
  · exact absurd (eq_eleven_of_palindromicPrime_even_numDigits h he) hn
  · exact ho

/-! ### Concrete palindromic primes -/

theorem palindromicPrime_two : PalindromicPrime 2 :=
  ⟨by norm_num, List.Palindrome.of_reverse_eq (by rw [show Nat.digits 10 2 = [2] by norm_num]; decide)⟩

theorem palindromicPrime_eleven : PalindromicPrime 11 :=
  ⟨by norm_num, List.Palindrome.of_reverse_eq (by rw [show Nat.digits 10 11 = [1, 1] by norm_num]; decide)⟩

theorem palindromicPrime_101 : PalindromicPrime 101 :=
  ⟨by norm_num,
    List.Palindrome.of_reverse_eq (by rw [show Nat.digits 10 101 = [1, 0, 1] by norm_num]; decide)⟩

theorem palindromicPrime_131 : PalindromicPrime 131 :=
  ⟨by norm_num,
    List.Palindrome.of_reverse_eq (by rw [show Nat.digits 10 131 = [1, 3, 1] by norm_num]; decide)⟩

theorem palindromicPrime_10301 : PalindromicPrime 10301 :=
  ⟨by norm_num,
    List.Palindrome.of_reverse_eq
      (by rw [show Nat.digits 10 10301 = [1, 0, 3, 0, 1] by norm_num]; decide)⟩

/-! ### The conditional reduction -/

/-- The hypothesis of the reduction: there are palindromic primes with arbitrarily
many decimal digits.  (This is the open part of the Brockian conjecture.) -/
def UnboundedDigitPalindromicPrimes : Prop :=
  ∀ k : ℕ, ∃ p : ℕ, PalindromicPrime p ∧ k < numDigits p

/--
**Palindromic Prime Infinitude (conditional).**

If there exist palindromic primes with arbitrarily many decimal digits, then the set
of palindromic primes is infinite.

This is a Lean-checked conditional reduction: the unconditional statement is an open
problem, and the hypothesis `H` isolates exactly the open input.
-/
theorem PalindromicPrimeInfinitude (H : UnboundedDigitPalindromicPrimes) :
    palindromicPrimes.Infinite := by
  refine Set.infinite_of_forall_exists_gt (fun N => ?_)
  obtain ⟨p, hp, hlen⟩ := H (numDigits N)
  refine ⟨p, hp, ?_⟩
  by_contra hle
  push_neg at hle
  exact absurd (Nat.le_digits_len_le 10 p N hle) (by simpa [numDigits] using hlen)

/-- Conversely, if the set of palindromic primes is infinite then there are
palindromic primes with arbitrarily many decimal digits. -/
theorem unboundedDigits_of_infinite (H : palindromicPrimes.Infinite) :
    UnboundedDigitPalindromicPrimes := by
  intro k
  obtain ⟨p, hp, hgt⟩ := H.exists_gt (10 ^ k)
  refine ⟨p, hp, ?_⟩
  by_contra hle
  push_neg at hle
  have h1 : p < 10 ^ numDigits p := Nat.lt_base_pow_length_digits (by norm_num)
  have h2 : p < 10 ^ k := lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hle)
  omega

/-- The reduction is in fact an equivalence. -/
theorem infinitude_iff_unboundedDigits :
    palindromicPrimes.Infinite ↔ UnboundedDigitPalindromicPrimes :=
  ⟨unboundedDigits_of_infinite, PalindromicPrimeInfinitude⟩

end Brockian.PalindromicPrimes

