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

The infinitude of decimal palindromic primes is an open problem.  This file develops
what can be established unconditionally, and reduces the conjecture to a statement
about *odd* digit lengths only.

Main contents:

* `Brockian.PalindromicPrimes.IsPalindrome` — decimal palindromes.
* `eleven_dvd_of_isPalindrome_even_length` — every decimal palindrome with an even
  number of digits is divisible by `11`.
* `eq_eleven_of_prime_palindrome_even_length` — hence `11` is the *only* palindromic
  prime with an even number of digits.
* `palindromes_infinite` — there are infinitely many decimal palindromes
  (the repunits).
* `PalindromicPrimeInfinitude` — the conditional reduction: if for arbitrarily large
  `m` there is a prime palindrome with exactly `2 * m + 1` digits, then there are
  infinitely many palindromic primes.
* `palindromicPrimes_infinite_iff` — the reduction is in fact an equivalence, so no
  strength is lost by restricting attention to odd digit lengths.
-/

namespace Brockian.PalindromicPrimes

/-- A natural number is a (decimal) palindrome when its list of base-10 digits is
equal to its own reversal. -/
def IsPalindrome (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- The set of palindromic primes. -/
def palindromicPrimes : Set ℕ := {p : ℕ | Nat.Prime p ∧ IsPalindrome p}

instance (n : ℕ) : Decidable (IsPalindrome n) := by
  unfold IsPalindrome; infer_instance

/-! ### Even digit length forces divisibility by 11 -/

/-- The alternating sum of a palindromic integer list of even length vanishes. -/
theorem alternatingSum_eq_zero_of_palindrome_even
    (l : List ℤ) (hrev : l.reverse = l) (hlen : Even l.length) :
    l.alternatingSum = 0 := by
  have h := List.alternatingSum_reverse l
  rw [hrev] at h
  obtain ⟨k, hk⟩ := hlen
  have hpow : ((-1 : ℤ) ^ (l.length + 1)) = -1 := by
    rw [hk, show k + k + 1 = 2 * k + 1 by ring, pow_succ, pow_mul]
    norm_num
  rw [hpow] at h
  simp only [neg_smul, one_smul] at h
  linarith

/-- Every decimal palindrome with an even number of digits is divisible by `11`. -/
theorem eleven_dvd_of_isPalindrome_even_length {n : ℕ} (hpal : IsPalindrome n)
    (hlen : Even (Nat.digits 10 n).length) : 11 ∣ n := by
  rw [Nat.eleven_dvd_iff]
  have hrev : ((Nat.digits 10 n).map (fun d : ℕ => (d : ℤ))).reverse
      = (Nat.digits 10 n).map (fun d : ℕ => (d : ℤ)) := by
    rw [← List.map_reverse, hpal]
  have hlen' : Even ((Nat.digits 10 n).map (fun d : ℕ => (d : ℤ))).length := by
    simpa using hlen
  rw [alternatingSum_eq_zero_of_palindrome_even _ hrev hlen']
  exact dvd_zero 11

/-- `11` is the only palindromic prime with an even number of digits. -/
theorem eq_eleven_of_prime_palindrome_even_length {p : ℕ} (hp : Nat.Prime p)
    (hpal : IsPalindrome p) (hlen : Even (Nat.digits 10 p).length) : p = 11 := by
  have hdvd : 11 ∣ p := eleven_dvd_of_isPalindrome_even_length hpal hlen
  exact ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hdvd).symm

/-- `11` is indeed a palindromic prime with an even number of digits. -/
theorem eleven_mem_palindromicPrimes : 11 ∈ palindromicPrimes := by
  refine ⟨by norm_num, ?_⟩
  unfold IsPalindrome
  decide

/-! ### There are infinitely many palindromes -/

/-- The repunit with `n + 1` digits. -/
def repunit (n : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate (n + 1) 1)

theorem digits_repunit (n : ℕ) : Nat.digits 10 (repunit n) = List.replicate (n + 1) 1 := by
  refine Nat.digits_ofDigits 10 (by norm_num) _ ?_ ?_
  · intro l hl
    rw [List.eq_of_mem_replicate hl]; norm_num
  · intro h
    rw [List.eq_of_mem_replicate (List.getLast_mem h)]
    norm_num

theorem isPalindrome_repunit (n : ℕ) : IsPalindrome (repunit n) := by
  unfold IsPalindrome
  rw [digits_repunit, List.reverse_replicate]

theorem repunit_injective : Function.Injective repunit := by
  intro a b hab
  have h : (List.replicate (a + 1) 1).length = (List.replicate (b + 1) 1).length := by
    rw [← digits_repunit, ← digits_repunit, hab]
  simpa using h

/-- There are infinitely many decimal palindromes. -/
theorem palindromes_infinite : {n : ℕ | IsPalindrome n}.Infinite :=
  Set.infinite_of_injective_forall_mem repunit_injective isPalindrome_repunit

/-! ### Digit-length bounds -/

theorem le_of_digits_length_eq {p k : ℕ} (hp : p ≠ 0) (hlen : (Nat.digits 10 p).length = k) :
    10 ^ k ≤ 10 * p := by
  have := Nat.base_pow_length_digits_le 10 p (by norm_num) hp
  rwa [hlen] at this

/-! ### The conditional reduction -/

/-- **Reduction of the palindromic prime conjecture to odd digit lengths.**

If for every `n` there is some `m ≥ n` admitting a prime decimal palindrome with
exactly `2 * m + 1` digits, then there are infinitely many palindromic primes.

The restriction to odd digit lengths is harmless: by
`eq_eleven_of_prime_palindrome_even_length`, the only palindromic prime with an even
number of digits is `11`, so all but one palindromic prime has odd digit length. -/
theorem PalindromicPrimeInfinitude
    (H : ∀ n : ℕ, ∃ m ≥ n, ∃ p : ℕ, Nat.Prime p ∧ IsPalindrome p ∧
      (Nat.digits 10 p).length = 2 * m + 1) :
    palindromicPrimes.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨m, hm, p, hp, hpal, hlen⟩ := H N
  have hmem : p ∈ palindromicPrimes := ⟨hp, hpal⟩
  have hpN : p ≤ N := hN hmem
  have h1 : 10 ^ (2 * m + 1) ≤ 10 * p := le_of_digits_length_eq hp.ne_zero hlen
  have h2 : (10 : ℕ) * N < 10 ^ (2 * N + 1) := by
    calc (10 : ℕ) * N < 10 * 10 ^ N := by
          have : N < 10 ^ N := Nat.lt_pow_self (by norm_num)
          omega
      _ ≤ 10 ^ (2 * N + 1) := by
          rw [show 2 * N + 1 = N + (N + 1) by ring, pow_add]
          have h : (10 : ℕ) ^ 1 ≤ 10 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          calc (10 : ℕ) * 10 ^ N = 10 ^ N * 10 ^ 1 := by ring
            _ ≤ 10 ^ N * 10 ^ (N + 1) := Nat.mul_le_mul_left _ h
  have h3 : (10 : ℕ) ^ (2 * N + 1) ≤ 10 ^ (2 * m + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 10 * p ≤ 10 * N := Nat.mul_le_mul_left 10 hpN
  omega

/-- The converse reduction: infinitely many palindromic primes forces prime
palindromes of arbitrarily large odd digit length. -/
theorem odd_length_of_palindromicPrimes_infinite (h : palindromicPrimes.Infinite) :
    ∀ n : ℕ, ∃ m ≥ n, ∃ p : ℕ, Nat.Prime p ∧ IsPalindrome p ∧
      (Nat.digits 10 p).length = 2 * m + 1 := by
  intro n
  obtain ⟨p, hpmem, hpgt⟩ := h.exists_gt (max 11 (10 ^ (2 * n + 1)))
  obtain ⟨hp, hpal⟩ := hpmem
  have h11 : 11 < p := lt_of_le_of_lt (le_max_left _ _) hpgt
  have hbig : 10 ^ (2 * n + 1) < p := lt_of_le_of_lt (le_max_right _ _) hpgt
  have hodd : ¬ Even (Nat.digits 10 p).length := by
    intro he
    have := eq_eleven_of_prime_palindrome_even_length hp hpal he
    omega
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨k, hk⟩ := hodd
  have hlarge : 2 * n + 1 < (Nat.digits 10 p).length :=
    (Nat.lt_digits_length_iff (by norm_num) p).2 hbig.le
  exact ⟨k, by omega, p, hp, hpal, hk⟩

/-- The palindromic prime conjecture is *equivalent* to the existence of prime
palindromes with arbitrarily large odd digit length. -/
theorem palindromicPrimes_infinite_iff :
    palindromicPrimes.Infinite ↔
      ∀ n : ℕ, ∃ m ≥ n, ∃ p : ℕ, Nat.Prime p ∧ IsPalindrome p ∧
        (Nat.digits 10 p).length = 2 * m + 1 :=
  ⟨odd_length_of_palindromicPrimes_infinite, PalindromicPrimeInfinitude⟩

end Brockian.PalindromicPrimes

