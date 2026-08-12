/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open Finset
open scoped ArithmeticFunction.sigma

namespace Brockian
namespace BetrothedNumbers

/-!
## Betrothed (quasi-amicable) pairs

A pair `(m, n)` of positive integers is *betrothed* (also called *quasi-amicable*, or a
*reduced amicable pair*) when each of the two numbers is the sum of the *nontrivial* proper
divisors of the other, i.e. `σ₁ m = σ₁ n = m + n + 1`.
-/

/-- `Betrothed m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
the sum of divisors of each of `m` and `n` equals `m + n + 1`. -/
def Betrothed (m n : ℕ) : Prop := σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-!
## Auxiliary results
-/

/-- A nonzero natural number is a perfect square iff all exponents in its prime factorization
are even. -/
theorem isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩ p _
    have hr : r ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul hr hr]
    simp
  · intro h
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    rw [← Finset.prod_mul_distrib]
    conv_lhs =>
      rw [← Nat.factorization_prod_pow_eq_self hn, Finsupp.prod, Nat.support_factorization]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    obtain ⟨k, hk⟩ := h p hp
    rw [hk, ← pow_add]
    congr 1
    omega

/-- A product of natural numbers is odd iff each factor is odd. -/
theorem odd_prod_iff (s : Finset ℕ) (f : ℕ → ℕ) :
    Odd (∏ p ∈ s, f p) ↔ ∀ p ∈ s, Odd (f p) := by
  simp only [← Nat.not_even_iff_odd, even_iff_two_dvd,
    Prime.dvd_finset_prod_iff Nat.prime_two.prime]
  push_neg
  rfl

/-- For an odd prime `p`, the geometric sum `1 + p + ⋯ + p ^ m` is odd iff `m` is even. -/
theorem odd_geom_sum_iff {p m : ℕ} (hp : p % 2 = 1) :
    Odd (∑ k ∈ Finset.range (m + 1), p ^ k) ↔ Even m := by
  have h : (∑ k ∈ Finset.range (m + 1), p ^ k) % 2 = (m + 1) % 2 := by
    rw [Finset.sum_nat_mod]; simp [Nat.pow_mod, hp]
  rw [Nat.odd_iff, h, Nat.even_iff]
  omega

/-- **Odd sum of divisors criterion.** For an odd positive `n`, the divisor sum `σ₁ n` is odd
exactly when `n` is a perfect square. -/
theorem odd_sigma_one_iff {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) :
    Odd (σ 1 n) ↔ IsSquare n := by
  have hoddp : ∀ p ∈ n.primeFactors, p % 2 = 1 := by
    intro p hp
    have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    rcases (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd with h2 | h1
    · subst h2
      rw [Nat.odd_iff] at hodd
      omega
    · exact h1
  have hfac : σ 1 n
      = ∏ p ∈ n.primeFactors, ∑ k ∈ Finset.range (n.factorization p + 1), p ^ k := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors hn]
  rw [hfac, odd_prod_iff, isSquare_iff_even_factorization hn]
  exact forall₂_congr fun p hp => odd_geom_sum_iff (hoddp p hp)

/-!
## The rational abundancy bound
-/

/-- For a prime `p`, the abundancy contribution of `p ^ a` is at most `p / (p - 1)`. -/
theorem geom_sum_div_pow_le {p a : ℕ} (hp : p.Prime) :
    (∑ k ∈ Finset.range (a + 1), (p : ℚ) ^ k) / (p : ℚ) ^ a ≤ (p : ℚ) / (p - 1) := by
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  have h1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hpa : (0 : ℚ) < (p : ℚ) ^ a := by positivity
  rw [div_le_div_iff₀ hpa h1]
  have hg : (∑ k ∈ Finset.range (a + 1), (p : ℚ) ^ k) * ((p : ℚ) - 1) = (p : ℚ) ^ (a + 1) - 1 :=
    geom_sum_mul (p : ℚ) (a + 1)
  have hs : (p : ℚ) ^ (a + 1) = (p : ℚ) * (p : ℚ) ^ a := by ring
  linarith

/-- **Rational abundancy bound.** For `N ≠ 0`, the abundancy index `σ₁ N / N` is at most
`∏_{p ∣ N} p / (p - 1)`, the product being over the distinct prime factors of `N`. -/
theorem abundancy_le_prod_primeFactors {N : ℕ} (hN : N ≠ 0) :
    (σ 1 N : ℚ) / N ≤ ∏ p ∈ N.primeFactors, (p : ℚ) / (p - 1) := by
  have hNq : (N : ℚ) = ∏ p ∈ N.primeFactors, (p : ℚ) ^ (N.factorization p) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast; ring
  have hσ : (σ 1 N : ℚ)
      = ∏ p ∈ N.primeFactors, (∑ k ∈ Finset.range (N.factorization p + 1), (p : ℚ) ^ k) := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors hN]
    push_cast; ring
  rw [hσ, hNq, ← Finset.prod_div_distrib]
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · positivity
  · exact geom_sum_div_pow_le (Nat.prime_of_mem_primeFactors hp)

/-!
## Extremality of the twenty smallest odd primes
-/

/-- The twenty smallest odd primes. -/
def smallOddPrimes : Finset ℕ :=
  {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73}

theorem card_smallOddPrimes : smallOddPrimes.card = 20 := by decide

theorem mem_smallOddPrimes {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hlt : p < 79) :
    p ∈ smallOddPrimes := by
  have h : ∀ q ∈ Finset.range 79, Nat.Prime q → q ≠ 2 → q ∈ smallOddPrimes := by decide
  exact h p (Finset.mem_range.mpr hlt) hp h2

theorem smallOddPrimes_bounds : ∀ p ∈ smallOddPrimes, 3 ≤ p ∧ p ≤ 73 := by decide

/-- Among sets of at most twenty odd primes, the twenty smallest odd primes maximise
`∏ p / (p - 1)`. -/
theorem prod_ratio_le_of_card_le {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hcard : S.card ≤ 20) :
    ∏ p ∈ S, (p : ℚ) / (p - 1) ≤ ∏ p ∈ smallOddPrimes, (p : ℚ) / (p - 1) := by
  classical
  have key1 : ∏ p ∈ S \ smallOddPrimes, (p : ℚ) / (p - 1)
      ≤ (79 / 78 : ℚ) ^ ((S \ smallOddPrimes).card) := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have h2 := (hS p (Finset.mem_sdiff.mp hp).1).1.two_le
      have h2' : (2 : ℚ) ≤ p := by exact_mod_cast h2
      have h1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
      positivity
    · obtain ⟨hpS, hpT⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hprime, hne⟩ := hS p hpS
      have h79 : 79 ≤ p := by
        by_contra hcon
        exact hpT (mem_smallOddPrimes hprime hne (by omega))
      have h79' : (79 : ℚ) ≤ p := by exact_mod_cast h79
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
  have key2 : ((73 : ℚ) / 72) ^ ((smallOddPrimes \ S).card)
      ≤ ∏ p ∈ smallOddPrimes \ S, (p : ℚ) / (p - 1) := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun p _ => by norm_num) (fun p hp => ?_)
    obtain ⟨h3, h73⟩ := smallOddPrimes_bounds p (Finset.mem_sdiff.mp hp).1
    have h3' : (3 : ℚ) ≤ p := by exact_mod_cast h3
    have h73' : (p : ℚ) ≤ 73 := by exact_mod_cast h73
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  have hcards : (S \ smallOddPrimes).card ≤ (smallOddPrimes \ S).card := by
    have h1 := Finset.card_sdiff_add_card_inter S smallOddPrimes
    have h2 := Finset.card_sdiff_add_card_inter smallOddPrimes S
    have h3 : (S ∩ smallOddPrimes).card = (smallOddPrimes ∩ S).card := by rw [Finset.inter_comm]
    have h4 := card_smallOddPrimes
    omega
  have step : (79 / 78 : ℚ) ^ ((S \ smallOddPrimes).card)
      ≤ (73 / 72 : ℚ) ^ ((smallOddPrimes \ S).card) :=
    le_trans (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
      (pow_le_pow_right₀ (by norm_num) hcards)
  have hpos : (0 : ℚ) < ∏ p ∈ S ∩ smallOddPrimes, (p : ℚ) / (p - 1) := by
    refine Finset.prod_pos (fun p hp => ?_)
    have h2 := (hS p (Finset.mem_inter.mp hp).1).1.two_le
    have h2' : (2 : ℚ) ≤ p := by exact_mod_cast h2
    have h1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
    positivity
  calc ∏ p ∈ S, (p : ℚ) / (p - 1)
      = (∏ p ∈ S ∩ smallOddPrimes, (p : ℚ) / (p - 1))
        * ∏ p ∈ S \ smallOddPrimes, (p : ℚ) / (p - 1) :=
        (Finset.prod_inter_mul_prod_diff S smallOddPrimes _).symm
    _ ≤ (∏ p ∈ S ∩ smallOddPrimes, (p : ℚ) / (p - 1))
        * ∏ p ∈ smallOddPrimes \ S, (p : ℚ) / (p - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hpos.le
        exact le_trans key1 (le_trans step key2)
    _ = (∏ p ∈ smallOddPrimes ∩ S, (p : ℚ) / (p - 1))
        * ∏ p ∈ smallOddPrimes \ S, (p : ℚ) / (p - 1) := by rw [Finset.inter_comm]
    _ = ∏ p ∈ smallOddPrimes, (p : ℚ) / (p - 1) :=
        Finset.prod_inter_mul_prod_diff smallOddPrimes S _

theorem prod_smallOddPrimes_lt_four :
    ∏ p ∈ smallOddPrimes, (p : ℚ) / (p - 1) < 4 := by decide +kernel

/-- An odd number whose abundancy index exceeds `4` has at least twenty-one distinct
prime factors. -/
theorem twentyOne_primeFactors_of_abundancy_gt_four {N : ℕ} (hN : N ≠ 0) (hodd : Odd N)
    (habund : 4 < (σ 1 N : ℚ) / N) : 21 ≤ N.primeFactors.card := by
  by_contra hcon
  have hcard : N.primeFactors.card ≤ 20 := by omega
  have hS : ∀ p ∈ N.primeFactors, p.Prime ∧ p ≠ 2 := by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    rintro rfl
    have h2 : 2 ∣ N := Nat.dvd_of_mem_primeFactors hp
    rw [Nat.odd_iff] at hodd
    omega
  have h1 := abundancy_le_prod_primeFactors hN
  have h2 := prod_ratio_le_of_card_le hS hcard
  have h3 := prod_smallOddPrimes_lt_four
  linarith

/-!
## The main theorem
-/

/-- **Second part of Hagis–Lord, Proposition 2.**
If `(m, n)` is a betrothed (quasi-amicable) pair with `gcd m n = 1` whose members have the same
parity, then both members are odd, each of them is a perfect square, and the product `m * n`
has at least twenty-one distinct prime factors. -/
theorem coprime_sameParity_twentyOne_primeFactors {m n : ℕ} (hb : Betrothed m n)
    (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    Odd m ∧ Odd n ∧ IsSquare m ∧ IsSquare n ∧ 21 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn⟩ := hb
  -- both members are nonzero
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp only [ArithmeticFunction.map_zero] at hm
    omega
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [ArithmeticFunction.map_zero] at hn
    omega
  -- coprimality plus equal parity forces both to be odd
  have hmodd : m % 2 = 1 := by
    by_contra hcon
    have hm2 : 2 ∣ m := by omega
    have hn2 : 2 ∣ n := by omega
    have : (2 : ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd hm2 hn2
    rw [hcop] at this
    omega
  have hnodd : n % 2 = 1 := by omega
  have hmO : Odd m := Nat.odd_iff.mpr hmodd
  have hnO : Odd n := Nat.odd_iff.mpr hnodd
  -- `m + n + 1` is odd, so both members are perfect squares
  have hsum_odd : Odd (m + n + 1) := by
    rw [Nat.odd_iff]; omega
  have hsqm : IsSquare m := (odd_sigma_one_iff hm0 hmO).mp (hm ▸ hsum_odd)
  have hsqn : IsSquare n := (odd_sigma_one_iff hn0 hnO).mp (hn ▸ hsum_odd)
  refine ⟨hmO, hnO, hsqm, hsqn, ?_⟩
  -- the abundancy index of `m * n` exceeds `4`
  set N := m * n with hNdef
  have hN0 : N ≠ 0 := Nat.mul_ne_zero hm0 hn0
  have hNodd : Odd N := hmO.mul hnO
  have hsigmaN : σ 1 N = (m + n + 1) ^ 2 := by
    rw [hNdef, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hm, hn, sq]
  have hNpos : (0 : ℚ) < (N : ℚ) := by positivity
  have habund : 4 < (σ 1 N : ℚ) / N := by
    rw [lt_div_iff₀ hNpos, hsigmaN]
    have hmq : (0 : ℚ) < (m : ℚ) := by positivity
    have hnq : (0 : ℚ) < (n : ℚ) := by positivity
    have hNq : (N : ℚ) = (m : ℚ) * (n : ℚ) := by rw [hNdef]; push_cast; ring
    rw [hNq]
    push_cast
    nlinarith [sq_nonneg ((m : ℚ) - (n : ℚ))]
  exact twentyOne_primeFactors_of_abundancy_gt_four hN0 hNodd habund

/-!
## Historical computational lower bounds (not formalized)

The theorem above is the *exact* statement proved by Hagis and Lord (1977): a coprime
betrothed pair whose two members have the same parity consists of two odd squares whose
product has at least twenty-one distinct prime factors.

Separately from this exact result, the literature records purely *computational* facts about
betrothed numbers — for instance exhaustive searches showing that no betrothed pair of equal
parity occurs below various search bounds. Such statements depend on large finite computations
and are **not** formalized here; nothing in this file assumes them, and the theorem above is
proved unconditionally.
-/

end BetrothedNumbers
end Brockian

