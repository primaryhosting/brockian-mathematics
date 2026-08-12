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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to be the very first command in a file, so the header module
-- docstring above sits immediately after the single `import Mathlib` line.)

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: they are distinct and each one's
sum of proper divisors is one more than the other, i.e. `σ(m) = σ(n) = m + n + 1`. -/
def Betrothed (m n : ℕ) : Prop :=
  m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- `n` is a square or twice a square. -/
def SquareOrTwiceSquare (n : ℕ) : Prop := IsSquare n ∨ ∃ k, n = 2 * k ^ 2

/-- Sanity check: `(48, 75)` is the smallest betrothed pair (`σ(48) = σ(75) = 124 = 48+75+1`).
Note that its two members have opposite parity, as in every known betrothed pair. -/
theorem betrothed_48_75 : Betrothed 48 75 := by
  refine ⟨by decide, ?_, ?_⟩ <;> (rw [sigmaOne]; decide)

/-! ### Parity of the divisor-sum -/

theorem isSquare_of_factorization_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  have key : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    have := Nat.factorization_prod_pow_eq_self hn
    rwa [Finsupp.prod, Nat.support_factorization] at this
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  have h2 : (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) *
      (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2))
      = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add]
    obtain ⟨k, hk⟩ := h p
    congr 1
    omega
  rw [h2, key]

/-- A number with an odd number of divisors is a square. -/
theorem isSquare_of_odd_card_divisors {n : ℕ} (hn : n ≠ 0) (h : Odd n.divisors.card) :
    IsSquare n := by
  refine isSquare_of_factorization_even hn fun p => ?_
  by_cases hp : p ∈ n.primeFactors
  · by_contra hev
    rw [Nat.not_even_iff_odd] at hev
    have hdvd : 2 ∣ (n.factorization p + 1) := by obtain ⟨k, hk⟩ := hev; omega
    have h2 : 2 ∣ ∏ x ∈ n.primeFactors, (n.factorization x + 1) :=
      hdvd.trans (Finset.dvd_prod_of_mem _ hp)
    rw [← Nat.card_divisors hn] at h2
    rw [Nat.odd_iff] at h
    omega
  · have : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [this]

/-- For odd `m`, the divisor sum has the same parity as the number of divisors. -/
theorem sigmaOne_mod_two_of_odd {m : ℕ} (hm : Odd m) :
    sigmaOne m % 2 = m.divisors.card % 2 := by
  rw [sigmaOne, Finset.sum_nat_mod]
  have h : ∀ d ∈ m.divisors, d % 2 = 1 := fun d hd =>
    Nat.odd_iff.mp (hm.of_dvd_nat (Nat.mem_divisors.mp hd).1)
  rw [Finset.sum_congr rfl h]
  simp

/-- An odd number with odd divisor sum is a square. -/
theorem isSquare_of_odd_of_odd_sigmaOne {m : ℕ} (hm : Odd m) (h : Odd (sigmaOne m)) :
    IsSquare m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  refine isSquare_of_odd_card_divisors hm0 ?_
  rw [Nat.odd_iff, ← sigmaOne_mod_two_of_odd hm, ← Nat.odd_iff]
  exact h

theorem sigmaOne_eq_sigma (n : ℕ) : sigmaOne n = ArithmeticFunction.sigma 1 n := by
  rw [ArithmeticFunction.sigma_one_apply, sigmaOne]

/-- Multiplicativity of the divisor sum at coprime arguments. -/
theorem sigmaOne_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    sigmaOne (a * b) = sigmaOne a * sigmaOne b := by
  simp only [sigmaOne_eq_sigma]
  exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

/-- Any number with an odd divisor sum is a square or twice a square. -/
theorem squareOrTwiceSquare_of_odd_sigmaOne {n : ℕ} (hn : n ≠ 0) (h : Odd (sigmaOne n)) :
    SquareOrTwiceSquare n := by
  set k := n.factorization 2 with hk
  set m := ordCompl[2] n with hmdef
  have hsplit : 2 ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_two hn)
  have hmodd : Odd m := Nat.odd_iff.mpr (by
    have := Nat.not_dvd_ordCompl Nat.prime_two hn
    omega)
  have hprod : sigmaOne n = sigmaOne (2 ^ k) * sigmaOne m := by
    rw [← hsplit, sigmaOne_mul_of_coprime hcop]
  have hoddm : Odd (sigmaOne m) := by
    rw [hprod] at h
    exact (Nat.odd_mul.mp h).2
  obtain ⟨j, hj⟩ := isSquare_of_odd_of_odd_sigmaOne hmodd hoddm
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨t, ht⟩ := he
    left
    refine ⟨2 ^ t * j, ?_⟩
    rw [← hsplit, hj, ht, pow_add]
    ring
  · obtain ⟨t, ht⟩ := ho
    right
    refine ⟨2 ^ t * j, ?_⟩
    rw [← hsplit, hj, ht, mul_pow, ← pow_mul]
    ring

/-! ### The converse: a full characterization of numbers with odd divisor sum -/

theorem even_factorization_of_isSquare {n : ℕ} (hn : n ≠ 0) (h : IsSquare n) (p : ℕ) :
    Even (n.factorization p) := by
  obtain ⟨j, hj⟩ := h
  have hj0 : j ≠ 0 := by rintro rfl; simp at hj; omega
  subst hj
  rw [Nat.factorization_mul hj0 hj0]
  simp [Finsupp.add_apply]

theorem odd_card_divisors_of_factorization_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : Odd n.divisors.card := by
  rw [Nat.card_divisors hn]
  refine Finset.prod_induction _ Odd (fun a b => Odd.mul) odd_one ?_
  intro p _
  obtain ⟨t, ht⟩ := h p
  exact ⟨t, by omega⟩

theorem odd_sigmaOne_two_pow (k : ℕ) : Odd (sigmaOne (2 ^ k)) := by
  rw [sigmaOne, Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      exact ih.add_even (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero n⟩)

/-- An odd square has odd divisor sum. -/
theorem odd_sigmaOne_of_odd_isSquare {m : ℕ} (hm : Odd m) (h : IsSquare m) :
    Odd (sigmaOne m) := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.odd_iff, sigmaOne_mod_two_of_odd hm, ← Nat.odd_iff]
  exact odd_card_divisors_of_factorization_even hm0 (even_factorization_of_isSquare hm0 h)

/-- Every square or twice a square (and nonzero) has odd divisor sum. -/
theorem odd_sigmaOne_of_squareOrTwiceSquare {n : ℕ} (hn : n ≠ 0) (h : SquareOrTwiceSquare n) :
    Odd (sigmaOne n) := by
  have hodd : ∀ p, p ≠ 2 → Even (n.factorization p) := by
    intro p hp
    rcases h with hsq | ⟨j, hj⟩
    · exact even_factorization_of_isSquare hn hsq p
    · have hj0 : j ≠ 0 := by rintro rfl; simp at hj; exact hn hj
      subst hj
      rw [Nat.factorization_mul two_ne_zero (pow_ne_zero 2 hj0)]
      simp [Nat.Prime.factorization Nat.prime_two, Ne.symm hp, Nat.factorization_pow]
  set k := n.factorization 2 with hk
  set m := ordCompl[2] n with hmdef
  have hsplit : 2 ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_two hn)
  have hmodd : Odd m := Nat.odd_iff.mpr (by
    have := Nat.not_dvd_ordCompl Nat.prime_two hn
    omega)
  have hm0 : m ≠ 0 := by rintro h0; rw [h0] at hmodd; simp at hmodd
  have hmsq : IsSquare m := by
    refine isSquare_of_factorization_even hm0 fun p => ?_
    rw [hmdef, Nat.factorization_ordCompl]
    by_cases hp : p = 2
    · subst hp; simp
    · rw [Finsupp.erase_ne hp]; exact hodd p hp
  rw [← hsplit, sigmaOne_mul_of_coprime hcop]
  exact (odd_sigmaOne_two_pow k).mul (odd_sigmaOne_of_odd_isSquare hmodd hmsq)

/-- **Characterization.** A nonzero natural number has odd sum of divisors if and only if it is
a square or twice a square. -/
theorem odd_sigmaOne_iff {n : ℕ} (hn : n ≠ 0) :
    Odd (sigmaOne n) ↔ SquareOrTwiceSquare n :=
  ⟨squareOrTwiceSquare_of_odd_sigmaOne hn, odd_sigmaOne_of_squareOrTwiceSquare hn⟩

/-! ### Structure of a same-parity betrothed pair -/

theorem Betrothed.ne_zero_left {m n : ℕ} (h : Betrothed m n) : m ≠ 0 := by
  rintro rfl
  have := h.2.1
  simp [sigmaOne] at this

theorem Betrothed.ne_zero_right {m n : ℕ} (h : Betrothed m n) : n ≠ 0 := by
  rintro rfl
  have := h.2.2
  simp [sigmaOne] at this

/-- In a same-parity betrothed pair, both divisor sums are odd. -/
theorem Betrothed.odd_sigmaOne {m n : ℕ} (h : Betrothed m n) (hpar : m % 2 = n % 2) :
    Odd (sigmaOne m) ∧ Odd (sigmaOne n) := by
  refine ⟨?_, ?_⟩
  · rw [h.2.1, Nat.odd_iff]; omega
  · rw [h.2.2, Nat.odd_iff]; omega

/-- **Structure theorem.** Each member of a same-parity betrothed pair is a square or twice
a square. -/
theorem Betrothed.squareOrTwiceSquare {m n : ℕ} (h : Betrothed m n) (hpar : m % 2 = n % 2) :
    SquareOrTwiceSquare m ∧ SquareOrTwiceSquare n :=
  ⟨squareOrTwiceSquare_of_odd_sigmaOne h.ne_zero_left (h.odd_sigmaOne hpar).1,
   squareOrTwiceSquare_of_odd_sigmaOne h.ne_zero_right (h.odd_sigmaOne hpar).2⟩

/-- **Odd case.** If both members of a betrothed pair are odd, both are odd squares. -/
theorem Betrothed.isSquare_of_odd {m n : ℕ} (h : Betrothed m n) (hm : Odd m) (hn : Odd n) :
    IsSquare m ∧ IsSquare n := by
  have hpar : m % 2 = n % 2 := by rw [Nat.odd_iff] at hm hn; omega
  exact ⟨isSquare_of_odd_of_odd_sigmaOne hm (h.odd_sigmaOne hpar).1,
    isSquare_of_odd_of_odd_sigmaOne hn (h.odd_sigmaOne hpar).2⟩

/-- **Conditional reduction for the existence of a same-parity betrothed pair.**

Whether a betrothed (quasi-amicable) pair of the same parity exists is an open problem: every
known betrothed pair consists of one even and one odd number. This theorem records a
Lean-checked reduction: a same-parity betrothed pair exists if and only if there is one in which
*both members are squares or twice squares*. The nontrivial direction is the structure theorem
above, obtained from the fact that `σ(m) = σ(n) = m + n + 1` is odd when `m` and `n` have equal
parity, together with the fact that a number has odd divisor sum exactly when it is a square or
twice a square. -/
theorem SameParityBetrothedExists :
    (∃ m n : ℕ, Betrothed m n ∧ m % 2 = n % 2) ↔
      (∃ m n : ℕ, Betrothed m n ∧ m % 2 = n % 2 ∧
        SquareOrTwiceSquare m ∧ SquareOrTwiceSquare n) := by
  constructor
  · rintro ⟨m, n, h, hpar⟩
    exact ⟨m, n, h, hpar, (h.squareOrTwiceSquare hpar).1, (h.squareOrTwiceSquare hpar).2⟩
  · rintro ⟨m, n, h, hpar, -, -⟩
    exact ⟨m, n, h, hpar⟩

end BetrothedNumbers
end Brockian

