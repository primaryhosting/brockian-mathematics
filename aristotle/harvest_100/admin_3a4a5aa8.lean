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

/-- `n` is a palindrome in base `b` if its list of base-`b` digits is equal to its reverse. -/
def IsPalindrome (b n : ℕ) : Prop := (Nat.digits b n).reverse = Nat.digits b n

instance (b n : ℕ) : Decidable (IsPalindrome b n) := by
  unfold IsPalindrome; infer_instance

/-- The set of base-10 palindromic primes. -/
def palindromicPrimes : Set ℕ := {p | Nat.Prime p ∧ IsPalindrome 10 p}

/-!
## The main reduction

Whether `palindromicPrimes` is infinite is a well-known open problem.  The theorem below is
the (unconditional) reduction of that statement to the statement that palindromic primes are
unbounded, i.e. that for every bound there is a larger palindromic prime.
-/

/-- **Reduction of the palindromic prime infinitude conjecture.**
The set of base-10 palindromic primes is infinite if and only if for every `N` there is a
palindromic prime larger than `N`. -/
theorem PalindromicPrimeInfinitude :
    palindromicPrimes.Infinite ↔
      ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ IsPalindrome 10 p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h.exists_gt N
    exact ⟨p, hlt, hp.1, hp.2⟩
  · intro h
    refine Set.infinite_of_forall_exists_gt ?_
    intro N
    obtain ⟨p, hlt, hp, hpal⟩ := h N
    exact ⟨p, ⟨hp, hpal⟩, hlt⟩

/-!
## Partial results

### Palindromes themselves are plentiful
-/

/-- The digit list `1 :: 0^k :: 1`, which is a palindrome of length `k + 2`. -/
def onePad (k : ℕ) : List ℕ := 1 :: (List.replicate k 0 ++ [1])

theorem onePad_reverse (k : ℕ) : (onePad k).reverse = onePad k := by
  simp [onePad, List.reverse_replicate]

theorem length_onePad (k : ℕ) : (onePad k).length = k + 2 := by
  simp [onePad]

theorem digits_ofDigits_onePad (k : ℕ) :
    Nat.digits 10 (Nat.ofDigits 10 (onePad k)) = onePad k := by
  refine Nat.digits_ofDigits 10 (by norm_num) _ ?_ ?_
  · intro l hl
    simp only [onePad, List.mem_cons, List.mem_append, List.mem_replicate] at hl
    simp only [List.not_mem_nil, or_false] at hl
    omega
  · intro h
    simp [onePad]

theorem isPalindrome_ofDigits_onePad (k : ℕ) :
    IsPalindrome 10 (Nat.ofDigits 10 (onePad k)) := by
  rw [IsPalindrome, digits_ofDigits_onePad, onePad_reverse]

/-- There are infinitely many base-10 palindromes (so the palindromic condition alone is not
an obstruction to infinitude). -/
theorem infinite_palindromes : {n : ℕ | IsPalindrome 10 n}.Infinite := by
  have hinj : Function.Injective fun k : ℕ => Nat.ofDigits 10 (onePad k) := by
    intro a b hab
    have hlist : onePad a = onePad b := by
      rw [← digits_ofDigits_onePad a, ← digits_ofDigits_onePad b]
      simp only at hab
      rw [hab]
    have := congrArg List.length hlist
    rw [length_onePad, length_onePad] at this
    omega
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => Nat.ofDigits 10 (onePad k))
    hinj ?_
  intro k
  exact isPalindrome_ofDigits_onePad k

/-!
### Even-length palindromic primes

Every base-10 palindrome with an even number of digits is divisible by 11; consequently `11`
is the only palindromic prime with an even number of digits.
-/

theorem alternatingSum_append_singleton (l : List ℤ) (x : ℤ) :
    (l ++ [x]).alternatingSum = l.alternatingSum + (-1) ^ l.length * x := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.cons_append, List.alternatingSum_cons, ih, List.alternatingSum_cons,
        List.length_cons, pow_succ]
      ring

theorem alternatingSum_eq_zero_of_palindrome_even
    {l : List ℤ} (hp : l.Palindrome) (hlen : Even l.length) :
    l.alternatingSum = 0 := by
  induction hp with
  | nil => simp
  | singleton x => simp at hlen
  | @cons_concat x m hl ih =>
      rw [List.length_cons, List.length_append, List.length_singleton] at hlen
      have hlen' : Even m.length := by
        rcases hlen with ⟨j, hj⟩
        exact ⟨j - 1, by omega⟩
      rw [List.alternatingSum_cons, alternatingSum_append_singleton, ih hlen',
        hlen'.neg_one_pow]
      ring

theorem eleven_dvd_of_isPalindrome_even_length {n : ℕ} (hpal : IsPalindrome 10 n)
    (hlen : Even (Nat.digits 10 n).length) : 11 ∣ n := by
  have hzero : ((Nat.digits 10 n).map (fun m : ℕ => (m : ℤ))).alternatingSum = 0 := by
    refine alternatingSum_eq_zero_of_palindrome_even (List.Palindrome.of_reverse_eq ?_) ?_
    · rw [← List.map_reverse, hpal]
    · simpa using hlen
  rw [Nat.eleven_dvd_iff, hzero]
  exact dvd_zero 11

/-- `11` is the only base-10 palindromic prime with an even number of digits. -/
theorem eq_eleven_of_palindromic_prime_even_length {p : ℕ} (hp : Nat.Prime p)
    (hpal : IsPalindrome 10 p) (hlen : Even (Nat.digits 10 p).length) : p = 11 := by
  have h11 : 11 ∣ p := eleven_dvd_of_isPalindrome_even_length hpal hlen
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 11 h11) with h | h
  · norm_num at h
  · exact h.symm

/-- Every palindromic prime other than `11` has an odd number of digits. -/
theorem odd_length_digits_of_palindromic_prime {p : ℕ} (hp : Nat.Prime p)
    (hpal : IsPalindrome 10 p) (hne : p ≠ 11) : Odd (Nat.digits 10 p).length := by
  rcases Nat.even_or_odd (Nat.digits 10 p).length with h | h
  · exact absurd (eq_eleven_of_palindromic_prime_even_length hp hpal h) hne
  · exact h

/-!
### Concrete palindromic primes
-/

theorem mem_palindromicPrimes_eleven : 11 ∈ palindromicPrimes := by
  refine ⟨by norm_num, ?_⟩
  rw [IsPalindrome]
  norm_num

theorem mem_palindromicPrimes_101 : 101 ∈ palindromicPrimes := by
  refine ⟨by norm_num, ?_⟩
  rw [IsPalindrome]
  norm_num

theorem mem_palindromicPrimes_1003001 : 1003001 ∈ palindromicPrimes := by
  refine ⟨by norm_num, ?_⟩
  rw [IsPalindrome]
  norm_num

/-- The set of palindromic primes with an even number of digits is exactly `{11}`. -/
theorem evenLength_palindromicPrimes_eq_singleton :
    {p ∈ palindromicPrimes | Even (Nat.digits 10 p).length} = {11} := by
  ext p
  constructor
  · rintro ⟨⟨hp, hpal⟩, hlen⟩
    exact eq_eleven_of_palindromic_prime_even_length hp hpal hlen
  · rintro rfl
    refine ⟨mem_palindromicPrimes_eleven, ?_⟩
    norm_num

end Brockian.PalindromicPrimes

