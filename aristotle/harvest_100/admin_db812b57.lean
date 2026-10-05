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

namespace Brockian.PalindromicPrimes

/-- `n` is a base-10 palindrome: its list of decimal digits is its own reverse. -/
def IsPalindrome (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- `n` is a palindromic prime: a prime number that is a base-10 palindrome. -/
def IsPalindromicPrime (n : ℕ) : Prop := Nat.Prime n ∧ IsPalindrome n

instance (n : ℕ) : Decidable (IsPalindrome n) := by
  unfold IsPalindrome; infer_instance

instance (n : ℕ) : Decidable (IsPalindromicPrime n) := by
  unfold IsPalindromicPrime; infer_instance

/-! ### Alternating sums of palindromic lists -/

private lemma alternatingSum_concat (l : List ℤ) (a : ℤ) :
    (l ++ [a]).alternatingSum = l.alternatingSum + (-1) ^ l.length * a := by
  induction l with
  | nil => simp
  | cons b t ih =>
      simp only [List.cons_append, List.alternatingSum_cons, ih, List.length_cons]
      ring

/-- A palindromic list of integers of even length has vanishing alternating sum. -/
lemma alternatingSum_eq_zero_of_palindrome_even {l : List ℤ}
    (hp : l.Palindrome) (he : Even l.length) : l.alternatingSum = 0 := by
  induction hp with
  | nil => simp
  | singleton a => simp at he
  | cons_concat a hq ih =>
      rename_i m
      have hlen : (a :: (m ++ [a])).length = m.length + 2 := by
        simp [List.length_append]
      rw [hlen] at he
      have hm : Even m.length := by
        rcases he with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
      have h0 : m.alternatingSum = 0 := ih hm
      have hpow : (-1 : ℤ) ^ m.length = 1 := hm.neg_one_pow
      rw [List.alternatingSum_cons, alternatingSum_concat, h0, hpow]
      ring

/-! ### Even-length palindromes are divisible by 11 -/

/-- Every base-10 palindrome with an even number of digits is divisible by `11`. -/
theorem eleven_dvd_of_palindrome_even_length {n : ℕ} (hp : IsPalindrome n)
    (he : Even (Nat.digits 10 n).length) : 11 ∣ n := by
  have hpal : (List.map (fun d : ℕ => (d : ℤ)) (Nat.digits 10 n)).Palindrome := by
    apply List.Palindrome.of_reverse_eq
    rw [← List.map_reverse, hp]
  have hlen : (List.map (fun d : ℕ => (d : ℤ)) (Nat.digits 10 n)).length
      = (Nat.digits 10 n).length := by simp
  have hsum : (List.map (fun d : ℕ => (d : ℤ)) (Nat.digits 10 n)).alternatingSum = 0 :=
    alternatingSum_eq_zero_of_palindrome_even hpal (by rw [hlen]; exact he)
  rw [Nat.eleven_dvd_iff, hsum]
  exact dvd_zero 11

/-- A palindromic prime with an even number of digits must be `11`. -/
theorem eq_eleven_of_palindromicPrime_even_length {n : ℕ} (h : IsPalindromicPrime n)
    (he : Even (Nat.digits 10 n).length) : n = 11 := by
  obtain ⟨hprime, hpal⟩ := h
  have hdvd : 11 ∣ n := eleven_dvd_of_palindrome_even_length hpal he
  rcases (Nat.Prime.eq_one_or_self_of_dvd hprime 11 hdvd) with h1 | h1
  · omega
  · omega

/-- Every palindromic prime other than `11` has an odd number of decimal digits. -/
theorem odd_length_of_palindromicPrime_ne_eleven {n : ℕ} (h : IsPalindromicPrime n)
    (hne : n ≠ 11) : Odd (Nat.digits 10 n).length := by
  rcases Nat.even_or_odd (Nat.digits 10 n).length with he | ho
  · exact absurd (eq_eleven_of_palindromicPrime_even_length h he) hne
  · exact ho

/-- `11` is a palindromic prime. -/
theorem isPalindromicPrime_eleven : IsPalindromicPrime 11 := by decide

/-! ### The main conditional reduction -/

/-- **Conditional reduction for the infinitude of palindromic primes.**

The unconditional infinitude of base-10 palindromic primes is an open problem, so the
statement is formulated conditionally: assuming palindromic primes are unbounded
(hypothesis `H`), the set of palindromic primes having an *odd* number of decimal digits
is infinite.  The "odd length" strengthening is genuine content: it rests on the
unconditional theorem, proved above, that `11` is the only palindromic prime with an
even number of decimal digits. -/
theorem PalindromicPrimeInfinitude
    (H : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsPalindromicPrime p) :
    {p : ℕ | IsPalindromicPrime p ∧ Odd (Nat.digits 10 p).length}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hp, hpp⟩ := H (max a 11)
  refine ⟨p, ⟨hpp, ?_⟩, lt_of_le_of_lt (le_max_left a 11) hp⟩
  exact odd_length_of_palindromicPrime_ne_eleven hpp
    (by have := lt_of_le_of_lt (le_max_right a 11) hp; omega)

/-- Conversely, if there are infinitely many palindromic primes then they are unbounded. -/
theorem unbounded_of_infinite_palindromicPrimes
    (h : {p : ℕ | IsPalindromicPrime p}.Infinite) :
    ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsPalindromicPrime p := by
  intro N
  obtain ⟨p, hp, hlt⟩ := h.exists_gt N
  exact ⟨p, hlt, hp⟩

/-- The infinitude of palindromic primes is equivalent to their unboundedness, and is
also equivalent to the infinitude of the odd-digit-length palindromic primes. -/
theorem palindromicPrimes_infinite_iff :
    {p : ℕ | IsPalindromicPrime p}.Infinite ↔
      {p : ℕ | IsPalindromicPrime p ∧ Odd (Nat.digits 10 p).length}.Infinite := by
  constructor
  · intro h
    exact PalindromicPrimeInfinitude (unbounded_of_infinite_palindromicPrimes h)
  · intro h
    exact h.mono (fun p hp => hp.1)

end Brockian.PalindromicPrimes

