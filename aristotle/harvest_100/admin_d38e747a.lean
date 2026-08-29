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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Two distinct positive integers `m`, `n` are *betrothed* (quasi-amicable) when the sum of the
proper divisors of each is one more than the other, i.e. `σ₁ m = σ₁ n = m + n + 1`.
All known betrothed pairs consist of one even and one odd number, and it is an open
problem whether a betrothed pair of equal parity exists.

This file proves a structural reduction for that open problem: in any same-parity betrothed
pair, each member is a perfect square or twice a perfect square (and if both members are odd,
each is a perfect square).  The main statement
`Brockian.BetrothedNumbers.SameParityBetrothedExists` records the resulting equivalence.
-/

namespace Brockian.BetrothedNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- A pair of *betrothed* (quasi-amicable) numbers: two distinct positive integers, each of
which is one less than the sum of the proper divisors of the other. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧
    (∑ d ∈ m.properDivisors, d) = n + 1 ∧ (∑ d ∈ n.properDivisors, d) = m + 1

/-- `n` is either a perfect square or twice a perfect square. -/
def SquareOrTwiceSquare (n : ℕ) : Prop := (∃ k, n = k ^ 2) ∨ (∃ k, n = 2 * k ^ 2)

/-- The smallest betrothed pair, `(48, 75)`; note that its members have opposite parity. -/
lemma betrothed_48_75 : Betrothed 48 75 :=
  ⟨by norm_num, by norm_num, by norm_num, by decide, by decide⟩

/-- `σ₁` is multiplicative. -/
lemma sigmaOne_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    sigmaOne (a * b) = sigmaOne a * sigmaOne b := by
  simpa [sigmaOne, ArithmeticFunction.sigma_one_apply] using
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime h

/-- `σ₁ (2 ^ a) = 2 ^ (a + 1) - 1` is odd. -/
lemma sigmaOne_two_pow_odd (a : ℕ) : Odd (sigmaOne (2 ^ a)) := by
  rw [sigmaOne, Nat.sum_divisors_prime_pow Nat.prime_two]
  induction a with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      exact ih.add_even ⟨2 ^ n, by ring⟩

/-- For an odd prime `p`, `σ₁ (p ^ k)` is odd only if `k` is even. -/
lemma even_of_odd_sigmaOne_odd_prime_pow {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (h : Odd (sigmaOne (p ^ k))) : Even k := by
  have hp2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · exact absurd h2 hodd
    · exact h2
  rw [sigmaOne, Nat.sum_divisors_prime_pow hp, Nat.odd_iff, Finset.sum_nat_mod] at h
  have key : ∀ i ∈ Finset.range (k + 1), p ^ i % 2 = 1 := by
    intro i _
    simp [Nat.pow_mod, hp2]
  rw [Finset.sum_congr rfl key] at h
  simp [Nat.even_iff] at h ⊢
  omega

/-- An odd number with odd sum of divisors is a perfect square. -/
lemma isSquare_of_odd_of_odd_sigmaOne : ∀ m : ℕ, Odd m → Odd (sigmaOne m) → ∃ t, m = t ^ 2 := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
      intro hm h
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact absurd hm (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hn.ne'⟩))
      obtain ⟨j, hj⟩ := even_of_odd_sigmaOne_odd_prime_pow hp hp2 h
      exact ⟨p ^ j, by rw [hj]; ring⟩
  | zero => intro hm _; simp at hm
  | one => intro _ _; exact ⟨1, by norm_num⟩
  | coprime a b _ _ hab iha ihb =>
      intro hm h
      rw [Nat.odd_mul] at hm
      rw [sigmaOne_mul_of_coprime hab, Nat.odd_mul] at h
      obtain ⟨s, hs⟩ := iha hm.1 h.1
      obtain ⟨t, ht⟩ := ihb hm.2 h.2
      exact ⟨s * t, by rw [hs, ht]; ring⟩

/-- A positive number with odd sum of divisors is a square or twice a square. -/
lemma squareOrTwiceSquare_of_odd_sigmaOne {n : ℕ} (hn : n ≠ 0) (h : Odd (sigmaOne n)) :
    SquareOrTwiceSquare n := by
  obtain ⟨k, m, hmo, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hmo)
  rw [sigmaOne_mul_of_coprime hcop, Nat.odd_mul] at h
  obtain ⟨t, rfl⟩ := isSquare_of_odd_of_odd_sigmaOne m hmo h.2
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact Or.inl ⟨2 ^ j * t, by subst hj; ring⟩
  · exact Or.inr ⟨2 ^ j * t, by subst hj; ring⟩

/-- Both members of a betrothed pair have sum of divisors `m + n + 1`. -/
lemma sigmaOne_eq_of_betrothed {m n : ℕ} (h : Betrothed m n) :
    sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1 := by
  obtain ⟨-, -, -, h1, h2⟩ := h
  constructor
  · rw [sigmaOne, Nat.sum_divisors_eq_sum_properDivisors_add_self, h1]; omega
  · rw [sigmaOne, Nat.sum_divisors_eq_sum_properDivisors_add_self, h2]; omega

/-- Any same-parity betrothed pair consists of two numbers each of which is a square or
twice a square. -/
theorem squareOrTwiceSquare_of_betrothed_of_sameParity {m n : ℕ} (h : Betrothed m n)
    (hpar : m % 2 = n % 2) : SquareOrTwiceSquare m ∧ SquareOrTwiceSquare n := by
  obtain ⟨hsm, hsn⟩ := sigmaOne_eq_of_betrothed h
  obtain ⟨hm0, hn0, -, -, -⟩ := h
  have hodd : Odd (m + n + 1) := by rw [Nat.odd_iff]; omega
  exact ⟨squareOrTwiceSquare_of_odd_sigmaOne hm0.ne' (hsm ▸ hodd),
    squareOrTwiceSquare_of_odd_sigmaOne hn0.ne' (hsn ▸ hodd)⟩

/-- If both members of a betrothed pair are odd, then both are perfect squares. -/
theorem isSquare_of_betrothed_of_odd {m n : ℕ} (h : Betrothed m n) (hm : Odd m) (hn : Odd n) :
    (∃ s, m = s ^ 2) ∧ (∃ t, n = t ^ 2) := by
  obtain ⟨hsm, hsn⟩ := sigmaOne_eq_of_betrothed h
  rw [Nat.odd_iff] at hm hn
  have hodd : Odd (m + n + 1) := by rw [Nat.odd_iff]; omega
  exact ⟨isSquare_of_odd_of_odd_sigmaOne m (Nat.odd_iff.mpr hm) (hsm ▸ hodd),
    isSquare_of_odd_of_odd_sigmaOne n (Nat.odd_iff.mpr hn) (hsn ▸ hodd)⟩

/-- **Conditional reduction for the same-parity case of the betrothed-numbers (Brockian)
conjecture.** A betrothed pair of equal parity exists if and only if one exists whose two
members are each a perfect square or twice a perfect square. -/
theorem SameParityBetrothedExists :
    (∃ m n, Betrothed m n ∧ m % 2 = n % 2) ↔
      (∃ m n, Betrothed m n ∧ m % 2 = n % 2 ∧
        SquareOrTwiceSquare m ∧ SquareOrTwiceSquare n) := by
  constructor
  · rintro ⟨m, n, h, hpar⟩
    obtain ⟨h1, h2⟩ := squareOrTwiceSquare_of_betrothed_of_sameParity h hpar
    exact ⟨m, n, h, hpar, h1, h2⟩
  · rintro ⟨m, n, h, hpar, -, -⟩
    exact ⟨m, n, h, hpar⟩

end Brockian.BetrothedNumbers

