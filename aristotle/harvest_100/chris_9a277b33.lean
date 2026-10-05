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

(Note: Lean 4 requires `import` commands to precede every other command, including
module docstrings, so the header above is a plain block comment `/- ... -/`; the same
text is repeated as the module docstring `/-! ... -/` immediately after the import.)
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

/-- `IsPalindromic b n` says that the base-`b` digit expansion of `n` reads the same
forwards and backwards. -/
def IsPalindromic (b n : ℕ) : Prop := (Nat.digits b n).reverse = Nat.digits b n

instance (b n : ℕ) : Decidable (IsPalindromic b n) :=
  inferInstanceAs (Decidable ((Nat.digits b n).reverse = Nat.digits b n))

theorem isPalindromic_iff_palindrome {b n : ℕ} :
    IsPalindromic b n ↔ (Nat.digits b n).Palindrome :=
  ⟨List.Palindrome.of_reverse_eq, List.Palindrome.reverse_eq⟩

/-- The digit list `1 :: 0^k ++ [1]`, i.e. the decimal palindrome `10 ^ (k+1) + 1`. -/
private def padList (k : ℕ) : List ℕ := 1 :: (List.replicate k 0 ++ [1])

private theorem padList_lt (k : ℕ) : ∀ l ∈ padList k, l < 10 := by
  intro l hl
  simp [padList, List.mem_replicate] at hl
  omega

private theorem padList_getLast (k : ℕ) (h : padList k ≠ []) :
    (padList k).getLast h ≠ 0 := by
  have heq : padList k = (1 :: List.replicate k 0) ++ [1] := by
    simp [padList, List.cons_append]
  rw [List.getLast_congr _ _ heq] <;> simp

private theorem padList_reverse (k : ℕ) : (padList k).reverse = padList k := by
  simp [padList, List.reverse_append, List.cons_append]

private theorem padList_length (k : ℕ) : (padList k).length = k + 2 := by
  simp [padList]

/-- There are infinitely many base-10 palindromes: only primality is at issue. -/
theorem palindromes_infinite : {n : ℕ | IsPalindromic 10 n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  have hd : Nat.digits 10 (Nat.ofDigits 10 (padList a)) = padList a :=
    Nat.digits_ofDigits 10 (by norm_num) _ (padList_lt a) (padList_getLast a)
  refine ⟨Nat.ofDigits 10 (padList a), ?_, ?_⟩
  · show IsPalindromic 10 _
    rw [IsPalindromic, hd, padList_reverse]
  · have hlen : a < (Nat.digits 10 (Nat.ofDigits 10 (padList a))).length := by
      rw [hd, padList_length]; omega
    have hle := (Nat.lt_digits_length_iff (b := 10) (by norm_num)
      (Nat.ofDigits 10 (padList a))).1 hlen
    calc a < 10 ^ a := Nat.lt_pow_self (by norm_num)
      _ ≤ _ := hle

/-- Every base-10 palindrome with an even number of digits is divisible by `11`. -/
theorem eleven_dvd_of_palindromic_even_length {n : ℕ} (hp : IsPalindromic 10 n)
    (he : Even (Nat.digits 10 n).length) : 11 ∣ n :=
  Nat.eleven_dvd_of_palindrome (isPalindromic_iff_palindrome.1 hp) he

/-- A palindromic prime other than `11` has an odd number of decimal digits. -/
theorem odd_length_of_palindromic_prime {p : ℕ} (hp : p.Prime) (hpal : IsPalindromic 10 p)
    (hne : p ≠ 11) : Odd (Nat.digits 10 p).length := by
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro he
  exact hne ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1
    (eleven_dvd_of_palindromic_even_length hpal he)).symm

/-- **Palindromic prime infinitude, reduced to a digit-length statement.**

The set of base-10 palindromic primes is infinite if and only if, for every `k`, there is a
palindromic prime with more than `k` decimal digits — and such a prime automatically has an
*odd* number of digits, since every even-length palindrome is divisible by `11`.

(The infinitude of base-10 palindromic primes is an open problem; this is a Lean-checked
equivalence, not a proof of either side.) -/
theorem PalindromicPrimeInfinitude :
    {p : ℕ | p.Prime ∧ IsPalindromic 10 p}.Infinite ↔
      ∀ k : ℕ, ∃ p : ℕ, p.Prime ∧ IsPalindromic 10 p ∧ k < (Nat.digits 10 p).length ∧
        Odd (Nat.digits 10 p).length := by
  constructor
  · intro hinf k
    obtain ⟨p, hpmem, hplt⟩ := hinf.exists_gt (10 ^ (k + 2))
    obtain ⟨hp, hpal⟩ := hpmem
    have hlen : k + 2 < (Nat.digits 10 p).length :=
      (Nat.lt_digits_length_iff (b := 10) (by norm_num) p).2 hplt.le
    have hne : p ≠ 11 := by
      rintro rfl
      norm_num at hlen
    exact ⟨p, hp, hpal, by omega, odd_length_of_palindromic_prime hp hpal hne⟩
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨p, hp, hpal, hlen, -⟩ := h a
    refine ⟨p, ⟨hp, hpal⟩, ?_⟩
    have hle : 10 ^ a ≤ p := (Nat.lt_digits_length_iff (b := 10) (by norm_num) p).1 hlen
    calc a < 10 ^ a := Nat.lt_pow_self (by norm_num)
      _ ≤ p := hle

end Brockian.PalindromicPrimes

