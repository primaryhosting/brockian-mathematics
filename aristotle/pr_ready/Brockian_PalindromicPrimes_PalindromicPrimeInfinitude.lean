/-!
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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


/-!
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Whether there are infinitely many base-10 palindromic primes is an open problem, so
what is proved here is an unconditional *reduction*: the infinitude of palindromic
primes is equivalent to the existence of arbitrarily large palindromic primes whose
decimal expansion has an **odd** number of digits.

The key intermediate lemma is that a base-10 palindrome with an even number of
digits is divisible by `11`; hence `11` is the only palindromic prime with an even
number of digits.
-/

namespace Brockian.PalindromicPrimes

open List

/-- `n` is a palindrome in base `b` if its list of base-`b` digits reads the same
backwards as forwards. -/
def IsPalindrome (b n : ℕ) : Prop := (Nat.digits b n).Palindrome

/-- The alternating sum of a palindromic list of even length vanishes. -/
theorem alternatingSum_eq_zero_of_palindrome_of_even_length :
    ∀ {l : List ℤ}, l.Palindrome → Even l.length → l.alternatingSum = 0 := by
  intro l hl
  induction hl with
  | nil => simp
  | singleton x => intro he; simp at he
  | @cons_concat x l _ ih =>
    intro he
    have hlen : Even l.length := by
      simpa [List.length_append, Nat.even_add_one, parity_simps] using he
    have h1 : (l ++ [x]).alternatingSum = l.alternatingSum + x := by
      simp [List.alternatingSum_append, hlen]
    simp [List.alternatingSum_cons, h1, ih hlen]

/-- **Key lemma.** A base-10 palindrome with an even number of digits is divisible by `11`. -/
theorem eleven_dvd_of_isPalindrome_of_even_length {n : ℕ} (hn : IsPalindrome 10 n)
    (he : Even (Nat.digits 10 n).length) : 11 ∣ n := by
  have hmap : ((Nat.digits 10 n).map (fun d : ℕ => (d : ℤ))).Palindrome := by
    refine List.Palindrome.of_reverse_eq ?_
    rw [← List.map_reverse, hn.reverse_eq]
  have hlen : Even ((Nat.digits 10 n).map (fun d : ℕ => (d : ℤ))).length := by
    simpa using he
  rw [Nat.eleven_dvd_iff,
    alternatingSum_eq_zero_of_palindrome_of_even_length hmap hlen]
  exact dvd_zero 11

/-- `11` is the only palindromic prime with an even number of decimal digits. -/
theorem eq_eleven_of_prime_of_isPalindrome_of_even_length {p : ℕ} (hp : p.Prime)
    (hpal : IsPalindrome 10 p) (he : Even (Nat.digits 10 p).length) : p = 11 :=
  ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp
    (eleven_dvd_of_isPalindrome_of_even_length hpal he)).symm

/-- Every palindromic prime other than `11` has an odd number of decimal digits. -/
theorem odd_length_digits_of_prime_of_isPalindrome {p : ℕ} (hp : p.Prime)
    (hpal : IsPalindrome 10 p) (hne : p ≠ 11) : Odd (Nat.digits 10 p).length := by
  rw [Nat.not_even_iff_odd.symm]
  exact fun he => hne (eq_eleven_of_prime_of_isPalindrome_of_even_length hp hpal he)

/-- The set of palindromic primes is nonempty: `131` is a palindromic prime (with an
odd number of digits, as the key lemma forces for every palindromic prime except `11`). -/
theorem prime_and_isPalindrome_131 : Nat.Prime 131 ∧ IsPalindrome 10 131 :=
  ⟨by norm_num, List.Palindrome.of_reverse_eq (by norm_num)⟩

/-- `11` is a palindromic prime, and it is the unique one with an even number of digits. -/
theorem prime_and_isPalindrome_eleven : Nat.Prime 11 ∧ IsPalindrome 10 11 :=
  ⟨by norm_num, List.Palindrome.of_reverse_eq (by norm_num)⟩

/-- **Reduction of the palindromic prime infinitude conjecture.**

There are infinitely many base-10 palindromic primes if and only if there are
arbitrarily large palindromic primes with an odd number of decimal digits. -/
theorem PalindromicPrimeInfinitude :
    {p : ℕ | p.Prime ∧ IsPalindrome 10 p}.Infinite ↔
      ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ IsPalindrome 10 p ∧
        Odd (Nat.digits 10 p).length := by
  constructor
  · intro hinf N
    obtain ⟨p, hpmem, hplt⟩ := hinf.exists_gt (max N 11)
    obtain ⟨hp, hpal⟩ := hpmem
    have hN : N < p := lt_of_le_of_lt (le_max_left N 11) hplt
    have hne : p ≠ 11 := by
      have : 11 < p := lt_of_le_of_lt (le_max_right N 11) hplt
      omega
    exact ⟨p, hN, hp, hpal, odd_length_digits_of_prime_of_isPalindrome hp hpal hne⟩
  · intro h
    refine Set.infinite_of_forall_exists_gt ?_
    intro a
    obtain ⟨p, hlt, hp, hpal, _⟩ := h a
    exact ⟨p, ⟨hp, hpal⟩, hlt⟩

end Brockian.PalindromicPrimes

