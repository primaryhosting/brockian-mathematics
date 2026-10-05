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
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the header above
-- is given as a plain block comment and repeated as the module docstring below.)

import Mathlib

/-!
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PalindromicPrimes

/-- `n` is a palindrome in base `b`: its list of base-`b` digits is its own reverse. -/
def IsPalindromic (b n : ℕ) : Prop :=
  Nat.digits b n = (Nat.digits b n).reverse

/-- A palindromic prime: a prime which is a palindrome in base ten. -/
def PalindromicPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ IsPalindromic 10 p

/-! ## Unconditional facts -/

/-- The alternating sum of a palindromic list of even length vanishes. -/
theorem alternatingSum_eq_zero_of_reverse_eq {l : List ℤ} (hpal : l = l.reverse)
    (hlen : Even l.length) : l.alternatingSum = 0 := by
  have h := List.alternatingSum_reverse l
  rw [← hpal] at h
  obtain ⟨m, hm⟩ := hlen
  have hpow : ((-1 : ℤ)) ^ (l.length + 1) = -1 := by
    rw [hm]
    have h2 : m + m + 1 = 2 * m + 1 := by ring
    rw [h2, pow_succ, pow_mul]
    norm_num
  rw [hpow] at h
  rw [neg_smul, one_smul] at h
  linarith

/-- Every base-ten palindrome with an even number of digits is divisible by `11`. -/
theorem eleven_dvd_of_palindromic_even_length {n : ℕ} (hpal : IsPalindromic 10 n)
    (hlen : Even (Nat.digits 10 n).length) : 11 ∣ n := by
  rw [Nat.eleven_dvd_iff]
  set l : List ℤ := (Nat.digits 10 n).map (fun d : ℕ => (d : ℤ)) with hl
  have hlpal : l = l.reverse := by
    rw [hl, ← List.map_reverse, ← hpal]
  have hllen : Even l.length := by simpa [hl] using hlen
  rw [alternatingSum_eq_zero_of_reverse_eq hlpal hllen]
  exact dvd_zero 11

/-- The only palindromic prime with an even number of digits is `11`. -/
theorem eq_eleven_of_palindromicPrime_even_length {p : ℕ} (hp : PalindromicPrime p)
    (hlen : Even (Nat.digits 10 p).length) : p = 11 := by
  obtain ⟨hprime, hpal⟩ := hp
  have h11 : 11 ∣ p := eleven_dvd_of_palindromic_even_length hpal hlen
  rcases hprime.eq_one_or_self_of_dvd 11 h11 with h | h
  · omega
  · exact h.symm

/-- The base-ten repunit with `k` digits. -/
def repunit (k : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate k 1)

theorem digits_repunit (k : ℕ) : Nat.digits 10 (repunit k) = List.replicate k 1 := by
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro l hl
    have := List.eq_of_mem_replicate hl
    omega
  · intro h
    have := List.eq_of_mem_replicate (List.getLast_mem h)
    omega

theorem isPalindromic_repunit (k : ℕ) : IsPalindromic 10 (repunit k) := by
  unfold IsPalindromic
  rw [digits_repunit]
  simp

/-- Repunits are palindromes with arbitrarily many digits, hence there are infinitely many
base-ten palindromes. -/
theorem infinite_palindromes : {n : ℕ | IsPalindromic 10 n}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => repunit (k + 1))
  · intro a b hab
    have hd : Nat.digits 10 (repunit (a + 1)) = Nat.digits 10 (repunit (b + 1)) := by
      simp only at hab
      rw [hab]
    rw [digits_repunit, digits_repunit] at hd
    have := congrArg List.length hd
    simpa using this
  · intro k
    exact isPalindromic_repunit (k + 1)

/-- Sanity checks: `11`, `101` and `131` are palindromic primes. -/
example : PalindromicPrime 11 := ⟨by norm_num, by simp [IsPalindromic]⟩

example : PalindromicPrime 101 := ⟨by norm_num, by simp [IsPalindromic]⟩

example : PalindromicPrime 131 := ⟨by norm_num, by simp [IsPalindromic]⟩

/-- Every prime is a one-digit, hence palindromic, numeral in any larger base, so there are
infinitely many primes that are palindromic in *some* base. -/
theorem infinite_primes_palindromic_in_some_base :
    {p : ℕ | Nat.Prime p ∧ ∃ b, 1 < b ∧ IsPalindromic b p}.Infinite := by
  apply Nat.infinite_setOf_prime.mono
  intro p hp
  refine ⟨hp, p + 1, hp.one_lt.trans (Nat.lt_succ_self p), ?_⟩
  have : Nat.digits (p + 1) p = [p] := Nat.digits_of_lt (p + 1) p hp.ne_zero (Nat.lt_succ_self p)
  simp [IsPalindromic, this]

/-! ## The conditional reduction -/

/-- A crude bound turning "many digits" into "large": a nonzero `n` has fewer than `10 * n`
base-ten digits. -/
theorem lt_of_digits_length {n : ℕ} (hn : n ≠ 0) : (Nat.digits 10 n).length < 10 * n := by
  have h1 : (10 : ℕ) ^ (Nat.digits 10 n).length ≤ 10 * n :=
    Nat.base_pow_length_digits_le 10 n (by norm_num) hn
  have h2 : (Nat.digits 10 n).length < 10 ^ (Nat.digits 10 n).length :=
    Nat.lt_pow_self (by norm_num)
  omega

/-- **Palindromic Prime Infinitude (conditional reduction).**

The unconditional infinitude of base-ten palindromic primes is an open problem.  What is
proved here is a reduction: if palindromic primes with arbitrarily many digits exist, then
there are infinitely many palindromic primes. -/
theorem PalindromicPrimeInfinitude
    (H : ∀ k : ℕ, ∃ p : ℕ, PalindromicPrime p ∧ k ≤ (Nat.digits 10 p).length) :
    {p : ℕ | PalindromicPrime p}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨p, hp, hlen⟩ := H (10 * N + 1)
  have hpN : p ≤ N := hN hp
  have hp0 : p ≠ 0 := hp.1.ne_zero
  have := lt_of_digits_length hp0
  omega

end Brockian.PalindromicPrimes

