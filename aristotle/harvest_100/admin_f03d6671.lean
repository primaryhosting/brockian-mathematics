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
def IsPalindrome (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

instance : DecidablePred IsPalindrome := fun _ => decEq _ _

/-- The set of palindromic primes. -/
def palindromicPrimes : Set ℕ := {p | Nat.Prime p ∧ IsPalindrome p}

/-! ## Examples -/

example : 2 ∈ palindromicPrimes := ⟨by norm_num, by simp [IsPalindrome]⟩
example : 11 ∈ palindromicPrimes := ⟨by norm_num, by norm_num [IsPalindrome]⟩
example : 101 ∈ palindromicPrimes := ⟨by norm_num, by norm_num [IsPalindrome]⟩
example : 131 ∈ palindromicPrimes := ⟨by norm_num, by norm_num [IsPalindrome]⟩
example : 929 ∈ palindromicPrimes := ⟨by norm_num, by norm_num [IsPalindrome]⟩

/-! ## Even-length palindromes are divisible by 11 -/

/-- The alternating sum of a palindromic integer list of even length vanishes. -/
theorem alternatingSum_eq_zero_of_palindrome_even
    (l : List ℤ) (hrev : l.reverse = l) (hlen : Even l.length) :
    l.alternatingSum = 0 := by
  have h := List.alternatingSum_reverse l
  rw [hrev] at h
  obtain ⟨m, hm⟩ := hlen
  have hodd : (-1 : ℤ) ^ (l.length + 1) = -1 := by
    rw [hm, show m + m + 1 = 2 * m + 1 by ring, pow_succ, pow_mul]
    norm_num
  rw [hodd] at h
  simp only [neg_smul, one_smul] at h
  linarith

/-- A palindromic number whose base-10 expansion has an even number of digits is
divisible by `11`. -/
theorem eleven_dvd_of_palindrome_even_length {n : ℕ} (hp : IsPalindrome n)
    (hlen : Even (Nat.digits 10 n).length) : 11 ∣ n := by
  rw [Nat.eleven_dvd_iff]
  have hrev : (List.map (fun m : ℕ => (m : ℤ)) (Nat.digits 10 n)).reverse
      = List.map (fun m : ℕ => (m : ℤ)) (Nat.digits 10 n) := by
    rw [← List.map_reverse, hp]
  have hlen' : Even (List.map (fun m : ℕ => (m : ℤ)) (Nat.digits 10 n)).length := by
    simpa using hlen
  rw [alternatingSum_eq_zero_of_palindrome_even _ hrev hlen']
  simp

/-- The only palindromic prime with an even number of base-10 digits is `11`. -/
theorem eq_eleven_of_palindromic_prime_even_length {p : ℕ} (hp : p ∈ palindromicPrimes)
    (hlen : Even (Nat.digits 10 p).length) : p = 11 := by
  obtain ⟨hprime, hpal⟩ := hp
  have h11 : 11 ∣ p := eleven_dvd_of_palindrome_even_length hpal hlen
  rcases hprime.eq_one_or_self_of_dvd 11 h11 with h | h
  · omega
  · exact h.symm

/-! ## There are arbitrarily large palindromes -/

/-- The digit list `[1, 0, 0, …, 0, 1]` (with `k` interior zeros). -/
def palList (k : ℕ) : List ℕ := 1 :: (List.replicate k 0 ++ [1])

theorem palList_reverse (k : ℕ) : (palList k).reverse = palList k := by
  simp [palList, List.reverse_replicate]

theorem palList_lt (k : ℕ) : ∀ d ∈ palList k, d < 10 := by
  intro d hd
  simp only [palList, List.mem_cons, List.mem_append, List.mem_replicate,
    ] at hd
  rcases hd with h | ⟨_, h⟩ | h | h <;> simp_all

theorem palList_getLast (k : ℕ) (h : palList k ≠ []) : (palList k).getLast h = 1 := by
  simp [palList, List.getLast_cons]

theorem palList_length (k : ℕ) : (palList k).length = k + 2 := by
  simp [palList]

theorem digits_palNumber (k : ℕ) :
    Nat.digits 10 (Nat.ofDigits 10 (palList k)) = palList k := by
  refine Nat.digits_ofDigits 10 (by norm_num) _ (palList_lt k) ?_
  intro h
  rw [palList_getLast k h]
  norm_num

/-- The number with digits `[1, 0, …, 0, 1]` is a palindrome. -/
theorem isPalindrome_palNumber (k : ℕ) : IsPalindrome (Nat.ofDigits 10 (palList k)) := by
  unfold IsPalindrome
  rw [digits_palNumber k, palList_reverse]

/-- There are palindromes with arbitrarily many digits, hence arbitrarily large ones. -/
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
theorem PalindromicPrimeInfinitude
    (h : ∀ k : ℕ, ∃ p, Nat.Prime p ∧ IsPalindrome p ∧ k < (Nat.digits 10 p).length) :
    palindromicPrimes.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro a
  obtain ⟨p, hprime, hpal, hlen⟩ := h a
  refine ⟨p, ⟨hprime, hpal⟩, ?_⟩
  have hne : p ≠ 0 := hprime.ne_zero
  have hle : (10 : ℕ) ^ (Nat.digits 10 p).length ≤ 10 * p :=
    Nat.base_pow_length_digits_le 10 p (by norm_num) hne
  have h1 : (10 : ℕ) ^ (a + 1) ≤ 10 ^ (Nat.digits 10 p).length :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : a < 10 ^ a := Nat.lt_pow_self (by norm_num)
  have h3 : (10:ℕ) ^ (a + 1) = 10 * 10 ^ a := by ring
  omega

end Brockian.PalindromicPrimes

