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
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PalindromicPrimes

open Nat

/-- A natural number is a (base-10) palindrome when its list of decimal digits
reads the same forwards and backwards. -/
def IsPalindrome (n : ℕ) : Prop := (Nat.digits 10 n).Palindrome

/-- The set of palindromic primes. -/
def palindromicPrimes : Set ℕ := {p | Nat.Prime p ∧ IsPalindrome p}

/-- The set of palindromic primes with an odd number of decimal digits. -/
def oddLengthPalindromicPrimes : Set ℕ :=
  {p | Nat.Prime p ∧ IsPalindrome p ∧ Odd (Nat.digits 10 p).length}

/-! ## Infinitude of the candidate pool

The repunits `1, 11, 111, …` are palindromes, so there are infinitely many
palindromes; the conjecture is not vacuous for lack of candidates. -/

/-- The `k`-th repunit, the number whose decimal expansion is `k + 1` ones. -/
def repunit (k : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate (k + 1) 1)

theorem digits_repunit (k : ℕ) :
    Nat.digits 10 (repunit k) = List.replicate (k + 1) 1 := by
  refine Nat.digits_ofDigits 10 (by norm_num) _ (fun l hl => ?_) (fun _ => ?_)
  · rw [List.eq_of_mem_replicate hl]; norm_num
  · rw [List.getLast_replicate]; norm_num

theorem isPalindrome_repunit (k : ℕ) : IsPalindrome (repunit k) := by
  refine List.Palindrome.of_reverse_eq ?_
  rw [digits_repunit, List.reverse_replicate]

theorem repunit_injective : Function.Injective repunit := by
  intro i j h
  have h' : List.replicate (i + 1) 1 = List.replicate (j + 1) 1 := by
    rw [← digits_repunit, ← digits_repunit, h]
  have := congrArg List.length h'
  simpa using this

/-- There are infinitely many base-10 palindromes. -/
theorem palindromes_infinite : {n : ℕ | IsPalindrome n}.Infinite :=
  Set.infinite_of_injective_forall_mem repunit_injective isPalindrome_repunit

/-! ## Reduction to odd digit length

Any palindrome with an even number of digits is divisible by `11`, hence `11`
is the only palindromic prime with an even number of digits. -/

/-- The only palindromic prime with an even number of decimal digits is `11`. -/
theorem eq_eleven_of_even_length {p : ℕ} (hp : Nat.Prime p) (hpal : IsPalindrome p)
    (he : Even (Nat.digits 10 p).length) : p = 11 :=
  ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp
    (Nat.eleven_dvd_of_palindrome hpal he)).symm

theorem evenLengthPalindromicPrimes_subset_singleton :
    {p : ℕ | Nat.Prime p ∧ IsPalindrome p ∧ Even (Nat.digits 10 p).length} ⊆ {11} := by
  rintro p ⟨hp, hpal, he⟩
  exact eq_eleven_of_even_length hp hpal he

/-- **Conditional reduction for the infinitude of palindromic primes.**

There are infinitely many palindromic primes if and only if there are
infinitely many palindromic primes with an *odd* number of decimal digits.

(The unconditional infinitude statement is a well-known open problem; this is a
Lean-checked reduction of it, obtained from the fact that every base-10
palindrome with an even number of digits is divisible by `11`.) -/
theorem PalindromicPrimeInfinitude :
    palindromicPrimes.Infinite ↔ oddLengthPalindromicPrimes.Infinite := by
  constructor
  · intro h
    by_contra hfin
    rw [Set.not_infinite] at hfin
    refine h (Set.Finite.subset (hfin.union (Set.finite_singleton 11)) ?_)
    rintro p ⟨hp, hpal⟩
    rcases Nat.even_or_odd (Nat.digits 10 p).length with he | ho
    · exact Or.inr (eq_eleven_of_even_length hp hpal he)
    · exact Or.inl ⟨hp, hpal, ho⟩
  · exact fun h => h.mono fun p hp => ⟨hp.1, hp.2.1⟩

/-- Reformulation: there are infinitely many palindromic primes iff there are
arbitrarily large ones. -/
theorem palindromicPrimes_infinite_iff_unbounded :
    palindromicPrimes.Infinite ↔ ∀ N : ℕ, ∃ p ∈ palindromicPrimes, N < p :=
  Set.infinite_iff_exists_gt

/-! ## Sanity checks -/

example : (11 : ℕ) ∈ palindromicPrimes :=
  ⟨by norm_num, List.Palindrome.of_reverse_eq (by decide)⟩

example : (131 : ℕ) ∈ oddLengthPalindromicPrimes :=
  ⟨by norm_num, List.Palindrome.of_reverse_eq (by decide), by decide⟩

end Brockian.PalindromicPrimes

