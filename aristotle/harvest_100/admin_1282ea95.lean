/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

/-- `σ₁ n` is the sum of divisors of `n`. -/
noncomputable def sigmaOne (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

/-- A pair `(m, n)` of positive integers is *betrothed* (quasi-amicable) when the sum of the
divisors of each of them equals `m + n + 1`. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- Geometric sum identity: `(∑_{i<a+1} p^i) * (p-1) + 1 = p^(a+1)`. -/
lemma geom_sum_mul_pred (p a : ℕ) (hp2 : 2 ≤ p) :
    (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) + 1 = p ^ (a + 1) := by
  induction a with
  | zero => simp; omega
  | succ k ih =>
      rw [Finset.sum_range_succ, add_mul, add_assoc, add_comm (p ^ (k + 1) * (p - 1)) 1,
        ← add_assoc, ih]
      have : p ^ (k + 1) * (p - 1) = p ^ (k + 1 + 1) - p ^ (k + 1) := by
        rw [Nat.mul_sub, mul_one, pow_succ]
        congr 1
      rw [this]
      have h1 : p ^ (k + 1) ≤ p ^ (k + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega

/-- `σ₁ (p ^ a) * (p - 1) + 1 = p ^ (a + 1)` for a prime `p`. -/
lemma sigmaOne_primePow_mul_pred (p a : ℕ) (hp : p.Prime) :
    sigmaOne (p ^ a) * (p - 1) + 1 = p ^ (a + 1) := by
  have hgeom : sigmaOne (p ^ a) = ∑ i ∈ Finset.range (a + 1), p ^ i := by
    rw [sigmaOne, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  rw [hgeom]
  exact geom_sum_mul_pred p a hp.two_le

/-- Termwise bound: `σ₁ (p ^ a) * (p - 1) ≤ p ^ a * p`. -/
lemma sigmaOne_primePow_bound (p a : ℕ) (hp : p.Prime) :
    sigmaOne (p ^ a) * (p - 1) ≤ p ^ a * p := by
  have := sigmaOne_primePow_mul_pred p a hp
  have hp' : p ^ a * p = p ^ (a + 1) := (pow_succ p a).symm
  omega

/-- The basic abundancy bound: `σ₁ N / N ≤ ∏_{p ∣ N} p / (p - 1)`, in cleared-denominator form. -/
lemma sigmaOne_mul_prod_pred_le (N : ℕ) (hN : N ≠ 0) :
    sigmaOne N * ∏ p ∈ N.primeFactors, (p - 1) ≤ N * ∏ p ∈ N.primeFactors, p := by
  have h1 : sigmaOne N = ∏ p ∈ N.primeFactors, sigmaOne (p ^ N.factorization p) := by
    rw [sigmaOne, ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hN,
      Finsupp.prod, Nat.support_factorization]
    rfl
  have h2 : N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rw [Finsupp.prod, Nat.support_factorization]
  have h3 : ∏ p ∈ N.primeFactors, (sigmaOne (p ^ N.factorization p) * (p - 1))
      ≤ ∏ p ∈ N.primeFactors, (p ^ N.factorization p * p) := by
    refine Finset.prod_le_prod' ?_
    intro p hp
    exact sigmaOne_primePow_bound p _ (Nat.prime_of_mem_primeFactors hp)
  calc sigmaOne N * ∏ p ∈ N.primeFactors, (p - 1)
      = ∏ p ∈ N.primeFactors, (sigmaOne (p ^ N.factorization p) * (p - 1)) := by
        rw [h1, ← Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ N.primeFactors, (p ^ N.factorization p * p) := h3
    _ = (∏ p ∈ N.primeFactors, p ^ N.factorization p) * ∏ p ∈ N.primeFactors, p := by
        rw [Finset.prod_mul_distrib]
    _ = N * ∏ p ∈ N.primeFactors, p := by rw [← h2]

/-- Three increasing primes: `4 * a * b * c ≤ 15 * (a-1) * (b-1) * (c-1)`. -/
lemma four_prod_le_three (a b c : ℕ) (hpa : a.Prime) (hpc : c.Prime)
    (hab : a < b) (hbc : b < c) :
    4 * (a * b * c) ≤ 15 * ((a - 1) * ((b - 1) * (c - 1))) := by
  have ha2 : 2 ≤ a := hpa.two_le
  have hb3 : 3 ≤ b := by omega
  have hc5 : 5 ≤ c := by
    have h4 : c ≠ 4 := by
      rintro rfl
      norm_num at hpc
    omega
  obtain ⟨A, rfl⟩ : ∃ A, a = A + 2 := ⟨a - 2, by omega⟩
  obtain ⟨B, rfl⟩ : ∃ B, b = B + 3 := ⟨b - 3, by omega⟩
  obtain ⟨C, rfl⟩ : ∃ C, c = C + 5 := ⟨c - 5, by omega⟩
  have e1 : A + 2 - 1 = A + 1 := by omega
  have e2 : B + 3 - 1 = B + 2 := by omega
  have e3 : C + 5 - 1 = C + 4 := by omega
  rw [e1, e2, e3]
  nlinarith [Nat.zero_le A, Nat.zero_le B, Nat.zero_le C, Nat.zero_le (A * B),
    Nat.zero_le (A * C), Nat.zero_le (B * C), Nat.zero_le (A * B * C)]

/-- Two increasing primes: `4 * a * b ≤ 15 * (a-1) * (b-1)`. -/
lemma four_prod_le_two (a b : ℕ) (hpa : a.Prime) (hab : a < b) :
    4 * (a * b) ≤ 15 * ((a - 1) * (b - 1)) := by
  have ha2 : 2 ≤ a := hpa.two_le
  have hb3 : 3 ≤ b := by omega
  obtain ⟨A, rfl⟩ : ∃ A, a = A + 2 := ⟨a - 2, by omega⟩
  obtain ⟨B, rfl⟩ : ∃ B, b = B + 3 := ⟨b - 3, by omega⟩
  have e1 : A + 2 - 1 = A + 1 := by omega
  have e2 : B + 3 - 1 = B + 2 := by omega
  rw [e1, e2]
  nlinarith [Nat.zero_le A, Nat.zero_le B, Nat.zero_le (A * B)]

/-- If a finite set of primes has at most three elements, then
`4 * ∏ p ≤ 15 * ∏ (p - 1)`; i.e. `∏ p/(p-1) ≤ 15/4`. -/
lemma four_prod_le_of_card_le_three (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 3) :
    4 * ∏ p ∈ S, p ≤ 15 * ∏ p ∈ S, (p - 1) := by
  interval_cases h : S.card
  · rw [Finset.card_eq_zero] at h
    subst h
    simp
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    have ha : (2 : ℕ) ≤ a := (hS a (by simp)).two_le
    simp only [Finset.prod_singleton]
    omega
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    have hpa := hS a (by simp)
    have hpb := hS b (by simp)
    rw [Finset.prod_pair hab, Finset.prod_pair hab]
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact four_prod_le_two a b hpa hlt
    · have := four_prod_le_two b a hpb hlt
      linarith
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h
    have hpa := hS a (by simp)
    have hpb := hS b (by simp)
    have hpc := hS c (by simp)
    have hprod : ∀ f : ℕ → ℕ, ∏ p ∈ ({a, b, c} : Finset ℕ), f p = f a * (f b * f c) := by
      intro f
      rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
        Finset.prod_singleton]
    rw [hprod (fun p => p), hprod (fun p => p - 1)]
    rcases lt_trichotomy a b with h1 | h1 | h1
    · rcases lt_trichotomy b c with h2 | h2 | h2
      · have := four_prod_le_three a b c hpa hpc h1 h2
        linarith [this]
      · exact absurd h2 hbc
      · rcases lt_trichotomy a c with h3 | h3 | h3
        · have := four_prod_le_three a c b hpa hpb h3 h2
          linarith [this]
        · exact absurd h3 hac
        · have := four_prod_le_three c a b hpc hpb h3 h1
          linarith [this]
    · exact absurd h1 hab
    · rcases lt_trichotomy a c with h2 | h2 | h2
      · have := four_prod_le_three b a c hpb hpc h1 h2
        linarith [this]
      · exact absurd h2 hac
      · rcases lt_trichotomy b c with h3 | h3 | h3
        · have := four_prod_le_three b c a hpb hpa h3 h2
          linarith [this]
        · exact absurd h3 hbc
        · have := four_prod_le_three c b a hpc hpa h3 h1
          linarith [this]

/-- Any positive integer whose set of prime factors has at most three elements satisfies
`4 * σ₁ N ≤ 15 * N`, in particular its abundancy index is at most `15/4 < 4`. -/
lemma four_mul_sigmaOne_le (N : ℕ) (hN : N ≠ 0) (hcard : N.primeFactors.card ≤ 3) :
    4 * sigmaOne N ≤ 15 * N := by
  have h1 := sigmaOne_mul_prod_pred_le N hN
  have h2 := four_prod_le_of_card_le_three N.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) hcard
  have hpos : 0 < ∏ p ∈ N.primeFactors, (p - 1) := by
    refine Finset.prod_pos ?_
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have key : (4 * sigmaOne N) * ∏ p ∈ N.primeFactors, (p - 1)
      ≤ (15 * N) * ∏ p ∈ N.primeFactors, (p - 1) := by
    calc (4 * sigmaOne N) * ∏ p ∈ N.primeFactors, (p - 1)
        = 4 * (sigmaOne N * ∏ p ∈ N.primeFactors, (p - 1)) := by ring
      _ ≤ 4 * (N * ∏ p ∈ N.primeFactors, p) := by exact Nat.mul_le_mul_left _ h1
      _ = N * (4 * ∏ p ∈ N.primeFactors, p) := by ring
      _ ≤ N * (15 * ∏ p ∈ N.primeFactors, (p - 1)) := Nat.mul_le_mul_left _ h2
      _ = (15 * N) * ∏ p ∈ N.primeFactors, (p - 1) := by ring
  exact Nat.le_of_mul_le_mul_right key hpos

/-- **Hagis–Lord, Proposition 2.** If `m` and `n` are coprime betrothed numbers, then `m * n`
has at least four distinct prime factors. -/
theorem coprime_pair_four_primeFactors {m n : ℕ} (h : Betrothed m n)
    (hcop : Nat.Coprime m n) : 4 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn, hsm, hsn⟩ := h
  by_contra hlt
  push_neg at hlt
  have hcard : (m * n).primeFactors.card ≤ 3 := by omega
  have hNne : m * n ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  -- multiplicativity of σ₁
  have hmul : sigmaOne (m * n) = sigmaOne m * sigmaOne n := by
    simpa [sigmaOne] using ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  have hbig : 4 * (m * n) < sigmaOne (m * n) := by
    rw [hmul, hsm, hsn]
    zify
    nlinarith [sq_nonneg ((m : ℤ) - (n : ℤ)), Int.natCast_pos.mpr hm, Int.natCast_pos.mpr hn]
  have hsmall := four_mul_sigmaOne_le (m * n) hNne hcard
  omega

end BetrothedNumbers
end Brockian

