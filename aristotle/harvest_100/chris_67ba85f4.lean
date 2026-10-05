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

/-- `IsPalindrome b n` says that the base-`b` digit expansion of `n` reads the same
forwards and backwards. -/
def IsPalindrome (b n : ℕ) : Prop := (Nat.digits b n).reverse = Nat.digits b n

instance (b n : ℕ) : Decidable (IsPalindrome b n) := by
  unfold IsPalindrome; infer_instance

/-- The set of base-10 palindromic primes. -/
def palindromicPrimes : Set ℕ := {p : ℕ | Nat.Prime p ∧ IsPalindrome 10 p}

/-! ### Basic facts about decimal length -/

/-- A number has at most as many decimal digits as its own value. -/
lemma digits_length_le_self (n : ℕ) : (Nat.digits 10 n).length ≤ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [Nat.digits_len 10 n (by norm_num) hn]
    exact Nat.log_lt_self 10 hn

/-- A number with at least `N` decimal digits is at least `N`. -/
lemma le_of_le_digits_length {N n : ℕ} (h : N ≤ (Nat.digits 10 n).length) : N ≤ n :=
  h.trans (digits_length_le_self n)

/-- If `n ≥ 10 ^ N` then `n` has at least `N` decimal digits. -/
lemma le_digits_length_of_pow_le {N n : ℕ} (h : 10 ^ N ≤ n) : N ≤ (Nat.digits 10 n).length := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact absurd h (by positivity : (0:ℕ) < 10 ^ N).not_ge
  rw [Nat.digits_len 10 n (by norm_num) hn]
  exact le_trans ((Nat.le_log_iff_pow_le (by norm_num) hn).2 h) (Nat.le_succ _)

/-! ### Even-length palindromes are divisible by 11 -/

/-- A palindromic list of even length has vanishing alternating sum. -/
lemma alternatingSum_eq_zero_of_palindrome_even (L : List ℤ) (hrev : L.reverse = L)
    (hlen : Even L.length) : L.alternatingSum = 0 := by
  have h := List.alternatingSum_reverse L
  rw [hrev, (hlen.add_one).neg_one_pow] at h
  simp only [neg_smul, one_smul] at h
  linarith

/-- Every base-10 palindrome with an even number of digits is divisible by `11`. -/
theorem eleven_dvd_of_palindrome_even_length {n : ℕ} (hp : IsPalindrome 10 n)
    (hlen : Even (Nat.digits 10 n).length) : 11 ∣ n := by
  rw [Nat.eleven_dvd_iff]
  have hrev : ((Nat.digits 10 n).map (fun d : ℕ => (d : ℤ))).reverse
      = (Nat.digits 10 n).map (fun d : ℕ => (d : ℤ)) := by
    rw [← List.map_reverse, hp]
  have hlen' : Even ((Nat.digits 10 n).map (fun d : ℕ => (d : ℤ))).length := by
    simpa using hlen
  rw [alternatingSum_eq_zero_of_palindrome_even _ hrev hlen']
  exact dvd_zero 11

/-- The only base-10 palindromic prime with an even number of digits is `11`.
Hence, apart from `11`, every palindromic prime has an odd number of digits. -/
theorem eq_eleven_of_prime_palindrome_even_length {p : ℕ} (hprime : Nat.Prime p)
    (hpal : IsPalindrome 10 p) (hlen : Even (Nat.digits 10 p).length) : p = 11 := by
  have h11 : 11 ∣ p := eleven_dvd_of_palindrome_even_length hpal hlen
  rcases hprime.eq_one_or_self_of_dvd 11 h11 with h | h
  · exact absurd h (by norm_num)
  · exact h.symm

/-- `101` is a palindromic prime, so the set of palindromic primes is nonempty. -/
theorem mem_palindromicPrimes_101 : (101 : ℕ) ∈ palindromicPrimes := by
  refine ⟨by norm_num, ?_⟩
  unfold IsPalindrome
  norm_num

/-- The first ten palindromic primes, checked in Lean. -/
theorem mem_palindromicPrimes_of_mem_sample :
    ∀ p ∈ [2, 3, 5, 7, 11, 101, 131, 151, 181, 191], p ∈ palindromicPrimes := by
  unfold palindromicPrimes IsPalindrome
  norm_num

/-! ### There are infinitely many palindromes -/

/-- The repunit `1…1` with `k + 1` digits has exactly the digit list `List.replicate (k+1) 1`. -/
lemma digits_repunit (k : ℕ) :
    Nat.digits 10 (Nat.ofDigits 10 (List.replicate (k + 1) 1)) = List.replicate (k + 1) 1 := by
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro l hl
    have := List.eq_of_mem_replicate hl
    omega
  · intro h
    have hm := List.getLast_mem h
    have := List.eq_of_mem_replicate hm
    omega

/-- Repunits are palindromes. -/
lemma isPalindrome_repunit (k : ℕ) :
    IsPalindrome 10 (Nat.ofDigits 10 (List.replicate (k + 1) 1)) := by
  unfold IsPalindrome
  rw [digits_repunit k, List.reverse_replicate]

/-- Unconditionally, there are infinitely many base-10 palindromes: the obstruction in the
conjecture lies entirely in the primality requirement. -/
theorem infinite_palindromes : {n : ℕ | IsPalindrome 10 n}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨M, hM⟩
  have hmem : Nat.ofDigits 10 (List.replicate (M + 1) 1) ∈ {n : ℕ | IsPalindrome 10 n} :=
    isPalindrome_repunit M
  have hle : Nat.ofDigits 10 (List.replicate (M + 1) 1) ≤ M := hM hmem
  have hlen : M + 1 ≤ (Nat.digits 10 (Nat.ofDigits 10 (List.replicate (M + 1) 1))).length := by
    rw [digits_repunit M, List.length_replicate]
  have := le_of_le_digits_length hlen
  omega

/-! ### The main conditional reduction -/

/--
**Palindromic Prime Infinitude (conditional reduction).**

Whether there are infinitely many base-10 palindromic primes is an open problem.
This theorem is the Lean-checked reduction: *if* palindromic primes with arbitrarily
many decimal digits exist, *then* the set of palindromic primes is infinite.
-/
theorem PalindromicPrimeInfinitude
    (H : ∀ N : ℕ, ∃ p : ℕ, Nat.Prime p ∧ IsPalindrome 10 p ∧ N ≤ (Nat.digits 10 p).length) :
    palindromicPrimes.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨M, hM⟩
  obtain ⟨p, hprime, hpal, hlen⟩ := H (M + 1)
  have h₁ : p ≤ M := hM ⟨hprime, hpal⟩
  have h₂ : M + 1 ≤ p := le_of_le_digits_length hlen
  omega

/-- The hypothesis of `PalindromicPrimeInfinitude` is in fact *equivalent* to the
infinitude of palindromic primes, so the reduction loses nothing. -/
theorem palindromicPrimeInfinitude_iff :
    (∀ N : ℕ, ∃ p : ℕ, Nat.Prime p ∧ IsPalindrome 10 p ∧ N ≤ (Nat.digits 10 p).length) ↔
      palindromicPrimes.Infinite := by
  refine ⟨PalindromicPrimeInfinitude, fun hinf N => ?_⟩
  obtain ⟨p, hp, hple⟩ := hinf.exists_gt (10 ^ N)
  exact ⟨p, hp.1, hp.2, le_digits_length_of_pow_le hple.le⟩

/--
Refinement of the reduction to *odd* decimal lengths: since `11` is the only
even-length palindromic prime, the set of palindromic primes is infinite if and only
if there are palindromic primes with arbitrarily many digits and an odd number of digits.
-/
theorem palindromicPrimeInfinitude_odd_length :
    (∀ N : ℕ, ∃ p : ℕ, Nat.Prime p ∧ IsPalindrome 10 p ∧ N ≤ (Nat.digits 10 p).length ∧
        Odd (Nat.digits 10 p).length) ↔ palindromicPrimes.Infinite := by
  rw [← palindromicPrimeInfinitude_iff]
  constructor
  · intro H N
    obtain ⟨p, hprime, hpal, hlen, -⟩ := H N
    exact ⟨p, hprime, hpal, hlen⟩
  · intro H N
    have hinf : palindromicPrimes.Infinite := PalindromicPrimeInfinitude H
    obtain ⟨p, hp, hgt⟩ := hinf.exists_gt (max (10 ^ N) 11)
    have hpow : 10 ^ N ≤ p := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hgt)
    have hodd : Odd (Nat.digits 10 p).length := by
      rw [Nat.not_even_iff_odd.symm]
      intro heven
      have : p = 11 := eq_eleven_of_prime_palindrome_even_length hp.1 hp.2 heven
      have : (11 : ℕ) < p := lt_of_le_of_lt (le_max_right _ _) hgt
      omega
    exact ⟨p, hp.1, hp.2, le_digits_length_of_pow_le hpow, hodd⟩

end Brockian.PalindromicPrimes

