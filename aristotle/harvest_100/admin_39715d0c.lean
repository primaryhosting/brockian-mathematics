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

-- (Lean does not permit a `/-!` module docstring before `import`; the header above is the
-- same text as a plain block comment, and is repeated as a module docstring below.)
import Mathlib

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers each of whose
sum of divisors equals `m + n + 1`. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- `n` is a square or twice a square. -/
def SquareOrTwiceSquare (n : ℕ) : Prop :=
  (∃ k, n = k ^ 2) ∨ (∃ k, n = 2 * k ^ 2)

/-- The smallest betrothed pair, `(48, 75)`; it has opposite parity, as do all known ones. -/
theorem betrothed_48_75 : Betrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;>
    simp [ArithmeticFunction.sigma_one_apply] <;> decide

/-- A positive natural number is a square iff all exponents in its factorization are even. -/
theorem isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    (∃ k, n = k ^ 2) ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨k, rfl⟩ p
    rw [Nat.factorization_pow]
    simp [Nat.two_mul]
  · intro h
    have key : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
      rw [← Nat.support_factorization]
      exact Nat.factorization_prod_pow_eq_self hn
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    rw [← Finset.prod_pow]
    have hcongr : ∀ p ∈ n.primeFactors,
        (p ^ (n.factorization p / 2)) ^ 2 = p ^ (n.factorization p) := by
      intro p _
      rw [← pow_mul]
      congr 1
      obtain ⟨c, hc⟩ := h p
      omega
    rw [Finset.prod_congr rfl hcongr, key]

/-- A positive natural number is a square or twice a square iff every odd prime occurs to an
even power in its factorization. -/
theorem squareOrTwiceSquare_iff {n : ℕ} (hn : n ≠ 0) :
    SquareOrTwiceSquare n ↔ ∀ p, p ≠ 2 → Even (n.factorization p) := by
  constructor
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩) p hp
    · exact (isSquare_iff_even_factorization hn).mp ⟨k, rfl⟩ p
    · have hk : k ≠ 0 := by rintro rfl; simp at hn
      rw [Nat.factorization_mul (by norm_num) (by positivity), Nat.factorization_pow]
      simp [Nat.Prime.factorization Nat.prime_two, hp, Nat.two_mul]
  · intro h
    rcases Nat.even_or_odd (n.factorization 2) with he | ho
    · left
      refine (isSquare_iff_even_factorization hn).mpr fun p => ?_
      by_cases hp : p = 2
      · subst hp; exact he
      · exact h p hp
    · right
      have h2 : 2 ∣ n := by
        refine (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn).mpr ?_
        rcases ho with ⟨c, hc⟩; omega
      obtain ⟨m, rfl⟩ := h2
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      have hfac : (2 * m).factorization = Nat.factorization 2 + m.factorization :=
        Nat.factorization_mul (by norm_num) hm
      have hsq : ∃ k, m = k ^ 2 := by
        refine (isSquare_iff_even_factorization hm).mpr fun p => ?_
        by_cases hp : p = 2
        · subst hp
          rw [hfac] at ho
          simp [Nat.Prime.factorization Nat.prime_two, Nat.odd_iff, Nat.even_iff] at ho ⊢
          omega
        · have hnp := h p hp
          rw [hfac] at hnp
          simpa [Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply,
            Ne.symm hp] using hnp
      obtain ⟨k, hk⟩ := hsq
      exact ⟨k, by rw [hk]⟩

/-- For odd `p`, the sum `∑_{i<k} p^i` has the same parity as `k`. -/
theorem geom_sum_mod_two {p : ℕ} (hp : Odd p) (k : ℕ) :
    (∑ i ∈ Finset.range k, p ^ i) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hpi : p ^ k % 2 = 1 := Nat.odd_iff.mp hp.pow
      rw [Finset.sum_range_succ]
      omega

/-- `∑_{i<k+1} 2^i` is odd. -/
theorem geom_sum_two_mod_two (k : ℕ) : (∑ i ∈ Finset.range (k + 1), 2 ^ i) % 2 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h2 : 2 ^ (k + 1) % 2 = 0 := by simp [Nat.pow_succ]
      rw [Finset.sum_range_succ]
      omega

/-- `σ n` is odd exactly when every odd prime occurs to an even power in `n`. -/
theorem odd_sigma_iff {n : ℕ} (hn : n ≠ 0) :
    Odd (σ 1 n) ↔ ∀ p, p ≠ 2 → Even (n.factorization p) := by
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp only [mul_one]
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero, Prime.dvd_finset_prod_iff Nat.prime_two.prime]
  push_neg
  constructor
  · intro hall p hp
    by_cases hmem : p ∈ n.primeFactors
    · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hmem
      have hodd : Odd p := hpp.odd_of_ne_two hp
      have h2 := hall p hmem
      rw [Nat.two_dvd_ne_zero, geom_sum_mod_two hodd] at h2
      rw [Nat.even_iff]; omega
    · have hz : n.factorization p = 0 := by
        rwa [← Finsupp.notMem_support_iff, Nat.support_factorization]
      simp [hz]
  · intro hall p hmem
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hmem
    by_cases hp : p = 2
    · subst hp
      rw [Nat.two_dvd_ne_zero, geom_sum_two_mod_two]
    · have hodd : Odd p := hpp.odd_of_ne_two hp
      rw [Nat.two_dvd_ne_zero, geom_sum_mod_two hodd]
      have h3 := hall p hp
      rw [Nat.even_iff] at h3; omega

/-- The sum of divisors of a number is odd exactly when it is a square or twice a square. -/
theorem odd_sigma_iff_squareOrTwiceSquare {n : ℕ} (hn : n ≠ 0) :
    Odd (σ 1 n) ↔ SquareOrTwiceSquare n := by
  rw [odd_sigma_iff hn, squareOrTwiceSquare_iff hn]

/--
**Same parity betrothed pairs.**

Whether a betrothed (quasi-amicable) pair of equal parity exists is an open problem, so what is
established here is an equivalent reformulation: a same-parity betrothed pair exists if and only
if a betrothed pair exists both of whose members are a square or twice a square.

The reduction rests on the fact that `σ m = m + n + 1` is odd exactly when `m` and `n` have the
same parity, together with the characterisation of the numbers with odd sum of divisors as the
squares and the doubles of squares.
-/
theorem SameParityBetrothedExists :
    (∃ m n, Betrothed m n ∧ m % 2 = n % 2) ↔
      (∃ m n, Betrothed m n ∧ SquareOrTwiceSquare m ∧ SquareOrTwiceSquare n) := by
  constructor
  · rintro ⟨m, n, hB, hpar⟩
    obtain ⟨hm, hn, hne, hsm, hsn⟩ := hB
    have hodd : Odd (m + n + 1) := by
      rw [Nat.odd_iff]; omega
    refine ⟨m, n, ⟨hm, hn, hne, hsm, hsn⟩, ?_, ?_⟩
    · exact (odd_sigma_iff_squareOrTwiceSquare hm.ne').mp (hsm ▸ hodd)
    · exact (odd_sigma_iff_squareOrTwiceSquare hn.ne').mp (hsn ▸ hodd)
  · rintro ⟨m, n, hB, hsq, -⟩
    obtain ⟨hm, hn, hne, hsm, hsn⟩ := hB
    have hodd : Odd (m + n + 1) :=
      hsm ▸ (odd_sigma_iff_squareOrTwiceSquare hm.ne').mpr hsq
    refine ⟨m, n, ⟨hm, hn, hne, hsm, hsn⟩, ?_⟩
    rw [Nat.odd_iff] at hodd
    omega

end Brockian.BetrothedNumbers

