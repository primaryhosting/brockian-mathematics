import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ArithmeticFunction.sigma

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Finset ArithmeticFunction

/-- A pair `(m, n)` of *betrothed* (a.k.a. quasi-amicable) numbers: each of the two numbers
is the sum of the *nontrivial* proper divisors of the other, i.e.
`σ m = m + n + 1` and `σ n = m + n + 1`.  As is customary the two members of the pair are
required to be distinct (this hypothesis is not needed for the theorem below). -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- Every prime is `2`, `3`, or at least `5`. -/
lemma prime_cast_cases {p : ℕ} (hp : p.Prime) : (p : ℤ) = 2 ∨ (p : ℤ) = 3 ∨ 5 ≤ (p : ℤ) := by
  have h2 : 2 ≤ p := hp.two_le
  rcases eq_or_lt_of_le h2 with h | h
  · exact Or.inl (by exact_mod_cast h.symm)
  have h3' : 3 ≤ p := h
  rcases eq_or_lt_of_le h3' with h3 | h3
  · exact Or.inr (Or.inl (by exact_mod_cast h3.symm))
  -- now `3 < p`, and `p ≠ 4` since `4` is not prime
  have h4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  have : 5 ≤ p := by omega
  exact Or.inr (Or.inr (by exact_mod_cast this))

/-- Bound for a single prime. -/
lemma one_bound {A : ℤ} (hA : A = 2 ∨ A = 3 ∨ 5 ≤ A) : A ≤ 4 * (A - 1) := by
  rcases hA with rfl | rfl | h <;> linarith

/-- Bound for two distinct primes. -/
lemma two_bound {A B : ℤ} (hA : A = 2 ∨ A = 3 ∨ 5 ≤ A) (hB : B = 2 ∨ B = 3 ∨ 5 ≤ B)
    (hAB : A ≠ B) : A * B ≤ 4 * ((A - 1) * (B - 1)) := by
  rcases hA with rfl | rfl | hA <;> rcases hB with rfl | rfl | hB <;>
    first
      | exact absurd rfl hAB
      | nlinarith [mul_pos (by linarith : (0:ℤ) < A) (by linarith : (0:ℤ) < B)]
      | nlinarith

/-- Bound for three distinct primes: the crucial numerical input is that
`2/1 * 3/2 * 5/4 = 15/4 < 4`. -/
lemma three_bound {A B C : ℤ} (hA : A = 2 ∨ A = 3 ∨ 5 ≤ A) (hB : B = 2 ∨ B = 3 ∨ 5 ≤ B)
    (hC : C = 2 ∨ C = 3 ∨ 5 ≤ C) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    A * (B * C) ≤ 4 * ((A - 1) * ((B - 1) * (C - 1))) := by
  rcases hA with rfl | rfl | hA <;> rcases hB with rfl | rfl | hB <;>
      rcases hC with rfl | rfl | hC <;>
    first
      | exact absurd rfl hAB
      | exact absurd rfl hAC
      | exact absurd rfl hBC
      | nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ B - 5) (by linarith : (0:ℤ) ≤ C - 5),
          mul_nonneg (by linarith : (0:ℤ) ≤ A - 5) (by linarith : (0:ℤ) ≤ B - 5),
          mul_nonneg (by linarith : (0:ℤ) ≤ A - 5) (by linarith : (0:ℤ) ≤ C - 5)]
      | nlinarith

/-- If a finite set of primes has at most three elements, then `∏ p ≤ 4 * ∏ (p - 1)`. -/
lemma prod_le_of_card_le_three (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 3) :
    ∏ p ∈ S, (p : ℤ) ≤ 4 * ∏ p ∈ S, ((p : ℤ) - 1) := by
  interval_cases h : S.card
  · rw [Finset.card_eq_zero] at h
    subst h
    simp
  · rw [Finset.card_eq_one] at h
    obtain ⟨a, rfl⟩ := h
    simp only [Finset.prod_singleton]
    exact one_bound (prime_cast_cases (hS a (by simp)))
  · rw [Finset.card_eq_two] at h
    obtain ⟨a, b, hab, rfl⟩ := h
    rw [Finset.prod_pair hab, Finset.prod_pair hab]
    exact two_bound (prime_cast_cases (hS a (by simp))) (prime_cast_cases (hS b (by simp)))
      (by exact_mod_cast hab)
  · rw [Finset.card_eq_three] at h
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := h
    rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc,
      Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc]
    exact three_bound (prime_cast_cases (hS a (by simp))) (prime_cast_cases (hS b (by simp)))
      (prime_cast_cases (hS c (by simp))) (by exact_mod_cast hab) (by exact_mod_cast hac)
      (by exact_mod_cast hbc)

/-- `σ (p ^ k) * (p - 1) = p ^ (k + 1) - 1` for a prime `p`. -/
lemma sigma_primePow_mul_sub_one {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((σ 1 (p ^ k) : ℕ) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) ^ (k + 1) - 1 := by
  have : σ 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
    rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  rw [this]
  push_cast
  rw [geom_sum_mul]

/-- The key inequality: `σ N * ∏_{p ∣ N} (p - 1) < N * ∏_{p ∣ N} p` for `N > 1`. -/
lemma sigma_mul_prod_sub_one_lt {N : ℕ} (hN : 1 < N) :
    ((σ 1 N : ℕ) : ℤ) * ∏ p ∈ N.primeFactors, ((p : ℤ) - 1)
      < (N : ℤ) * ∏ p ∈ N.primeFactors, (p : ℤ) := by
  have hN0 : N ≠ 0 := by omega
  have hσ : ((σ 1 N : ℕ) : ℤ)
      = ∏ p ∈ N.primeFactors, ((σ 1 (p ^ N.factorization p) : ℕ) : ℤ) := by
    have := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
      (σ 1) ArithmeticFunction.isMultiplicative_sigma hN0
    rw [this, Finsupp.prod, Nat.support_factorization, Nat.cast_prod]
  have hNe : (N : ℤ) = ∏ p ∈ N.primeFactors, (p : ℤ) ^ N.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN0]
    rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod]
    push_cast
    rfl
  rw [hσ, hNe, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_lt_prod_of_nonempty ?_ ?_ (Nat.nonempty_primeFactors.2 hN)
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hpp.two_le
    have hσpos : (0 : ℤ) < ((σ 1 (p ^ N.factorization p) : ℕ) : ℤ) := by
      have : 0 < σ 1 (p ^ N.factorization p) :=
        ArithmeticFunction.sigma_pos 1 _ (pow_ne_zero _ hpp.pos.ne')
      exact_mod_cast this
    have : (0 : ℤ) < (p : ℤ) - 1 := by linarith
    positivity
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [sigma_primePow_mul_sub_one hpp]
    have : (p : ℤ) ^ N.factorization p * (p : ℤ) = (p : ℤ) ^ (N.factorization p + 1) := by
      ring
    rw [this]
    linarith

/-- **Hagis–Lord, Proposition 2.**  If `m` and `n` are coprime betrothed numbers then
`m * n` has at least four distinct prime factors. -/
theorem coprime_pair_four_primeFactors {m n : ℕ} (h : Betrothed m n)
    (hco : Nat.Coprime m n) : 4 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn, -, hsm, hsn⟩ := h
  set N := m * n with hNdef
  have hN0 : 0 < N := Nat.mul_pos hm hn
  -- abundancy: σ N = (m + n + 1) ^ 2 > 4 * N
  have hmul : σ 1 N = (m + n + 1) * (m + n + 1) := by
    rw [hNdef, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hco, hsm, hsn]
  have habund : 4 * N < σ 1 N := by
    rw [hmul, hNdef]
    nlinarith [two_mul_le_add_sq m n, hm, hn]
  have hN1 : 1 < N := by
    by_contra hc
    have hN1' : N = 1 := by omega
    rw [hN1', ArithmeticFunction.sigma_one] at habund
    omega
  by_contra hcard
  push_neg at hcard
  have hcard3 : N.primeFactors.card ≤ 3 := by omega
  have hprod := prod_le_of_card_le_three N.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) hcard3
  have hkey := sigma_mul_prod_sub_one_lt hN1
  have hposP : (0 : ℤ) < ∏ p ∈ N.primeFactors, ((p : ℤ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hpp.two_le
    linarith
  have hab : (4 : ℤ) * (N : ℤ) < ((σ 1 N : ℕ) : ℤ) := by exact_mod_cast habund
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN0
  nlinarith [mul_lt_mul_of_pos_right hab hposP, hkey,
    mul_le_mul_of_nonneg_left hprod (le_of_lt hNpos), hNpos, hposP]

end BetrothedNumbers
end Brockian

