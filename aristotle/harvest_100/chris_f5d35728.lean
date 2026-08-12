/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat
open scoped ArithmeticFunction.sigma

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

/-- `Betrothed m n` says that `m` and `n` form a pair of betrothed (quasi-amicable)
numbers: they are distinct positive integers each of whose sum of divisors equals
`m + n + 1` (equivalently, the sum of the *proper* divisors of each, excluding `1`
and the number itself, is the other number). -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- Geometric-sum bound: `(p - 1) * (1 + p + ⋯ + p ^ (k - 1)) ≤ p ^ k`. -/
lemma pred_mul_geom_sum_le (p k : ℕ) : (p - 1) * ∑ i ∈ Finset.range k, p ^ i ≤ p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp
      · rw [Finset.sum_range_succ, Nat.mul_add, pow_succ]
        have h1 : (p - 1) * p ^ k + p ^ k = p * p ^ k := by
          have : (p - 1) * p ^ k + 1 * p ^ k = (p - 1 + 1) * p ^ k := by ring
          simp only [one_mul] at this
          rw [this, Nat.sub_add_cancel hp]
        calc (p - 1) * ∑ i ∈ Finset.range k, p ^ i + (p - 1) * p ^ k
            ≤ p ^ k + (p - 1) * p ^ k := Nat.add_le_add_right ih _
          _ = p * p ^ k := by omega
          _ = p ^ k * p := by ring

/-- The basic abundancy bound: `σ(N) * ∏_{p ∣ N} (p - 1) ≤ N * ∏_{p ∣ N} p`. -/
lemma sigma_mul_prod_pred_le (N : ℕ) (hN : N ≠ 0) :
    (∏ p ∈ N.primeFactors, (p - 1)) * σ 1 N ≤ (∏ p ∈ N.primeFactors, p) * N := by
  have hself : ∏ p ∈ N.primeFactors, p ^ N.factorization p = N := by
    rw [← Nat.support_factorization]
    exact Nat.factorization_prod_pow_eq_self hN
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hN,
    ← Finset.prod_mul_distrib]
  calc ∏ p ∈ N.primeFactors, ((p - 1) * ∑ i ∈ Finset.range (N.factorization p + 1), p ^ (i * 1))
      ≤ ∏ p ∈ N.primeFactors, p ^ (N.factorization p + 1) := by
        refine Finset.prod_le_prod' ?_
        intro p _
        simpa [mul_one] using pred_mul_geom_sum_le p (N.factorization p + 1)
    _ = (∏ p ∈ N.primeFactors, p) * N := by
        rw [show (∏ p ∈ N.primeFactors, p) * N
              = ∏ p ∈ N.primeFactors, p * p ^ N.factorization p from by
          rw [Finset.prod_mul_distrib, hself]]
        exact Finset.prod_congr rfl fun p _ => by ring

/-- The core inequality for three ordered quantities `x + 1 < y + 1 < z + 1`. -/
lemma three_core (x y z : ℕ) (hx : 1 ≤ x) (hy : 2 ≤ y) (hz : 4 ≤ z) :
    (x + 1) * (y + 1) * (z + 1) ≤ 4 * (x * y * z) := by
  obtain ⟨a, rfl⟩ : ∃ a, x = 1 + a := ⟨x - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = 2 + b := ⟨y - 2, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, z = 4 + c := ⟨z - 4, by omega⟩
  nlinarith [Nat.zero_le a, Nat.zero_le b, Nat.zero_le c, Nat.zero_le (a * b),
    Nat.zero_le (a * c), Nat.zero_le (b * c), Nat.zero_le (a * b * c)]

/-- For three distinct positive integers none of which equals `3` (this holds for
`p - 1` with `p` prime, since `4` is not prime), the product bound holds. -/
lemma three_bound (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (ha3 : a ≠ 3) (hb3 : b ≠ 3) (hc3 : c ≠ 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a + 1) * (b + 1) * (c + 1) ≤ 4 * (a * b * c) := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · rcases lt_trichotomy b c with h2 | h2 | h2
    · linarith [three_core a b c (by omega) (by omega) (by omega)]
    · omega
    · rcases lt_trichotomy a c with h3 | h3 | h3
      · linarith [three_core a c b (by omega) (by omega) (by omega)]
      · omega
      · linarith [three_core c a b (by omega) (by omega) (by omega)]
  · omega
  · rcases lt_trichotomy a c with h2 | h2 | h2
    · linarith [three_core b a c (by omega) (by omega) (by omega)]
    · omega
    · rcases lt_trichotomy b c with h3 | h3 | h3
      · linarith [three_core b c a (by omega) (by omega) (by omega)]
      · omega
      · linarith [three_core c b a (by omega) (by omega) (by omega)]

/-- If a finite set of primes has at most three elements, then the product of its
elements is at most four times the product of their predecessors. -/
lemma prod_le_four_mul_prod_pred {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 3) :
    ∏ p ∈ S, p ≤ 4 * ∏ p ∈ S, (p - 1) := by
  interval_cases h : S.card
  · rw [Finset.card_eq_zero] at h
    subst h; simp
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
    have ha := hS a (by simp)
    have : 2 ≤ a := ha.two_le
    simp only [Finset.prod_singleton]
    omega
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 h
    have ha := (hS a (by simp)).two_le
    have hb := (hS b (by simp)).two_le
    rw [Finset.prod_pair hab, Finset.prod_pair hab]
    obtain ⟨x, rfl⟩ : ∃ x, a = x + 1 := ⟨a - 1, by omega⟩
    obtain ⟨y, rfl⟩ : ∃ y, b = y + 1 := ⟨b - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 h
    have hpa := hS a (by simp)
    have hpb := hS b (by simp)
    have hpc := hS c (by simp)
    have ha := hpa.two_le
    have hb := hpb.two_le
    have hc := hpc.two_le
    have ha4 : a ≠ 4 := by rintro rfl; norm_num at hpa
    have hb4 : b ≠ 4 := by rintro rfl; norm_num at hpb
    have hc4 : c ≠ 4 := by rintro rfl; norm_num at hpc
    have hprod : ∀ f : ℕ → ℕ, ∏ p ∈ ({a, b, c} : Finset ℕ), f p = f a * (f b * f c) := by
      intro f
      rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
        Finset.prod_singleton]
    rw [hprod (fun p => p), hprod (fun p => p - 1)]
    obtain ⟨x, rfl⟩ : ∃ x, a = x + 1 := ⟨a - 1, by omega⟩
    obtain ⟨y, rfl⟩ : ∃ y, b = y + 1 := ⟨b - 1, by omega⟩
    obtain ⟨z, rfl⟩ : ∃ z, c = z + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have := three_bound x y z (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    linarith

/-- **Hagis–Lord, Proposition 2.** If `m` and `n` are coprime betrothed
(quasi-amicable) numbers, then `m * n` has at least four distinct prime factors. -/
theorem coprime_pair_four_primeFactors {m n : ℕ} (h : Betrothed m n)
    (hcop : Nat.Coprime m n) : 4 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn, _, hsm, hsn⟩ := h
  set N := m * n with hNdef
  have hN : N ≠ 0 := by positivity
  -- σ is multiplicative on coprime arguments
  have hsigma : σ 1 N = (m + n + 1) * (m + n + 1) := by
    rw [hNdef, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsm, hsn]
  -- the abundancy of `N` exceeds `4`
  have habund : 4 * N < σ 1 N := by
    have h2 : 2 * m * n ≤ m * m + n * n := by
      zify
      nlinarith [sq_nonneg ((m : ℤ) - (n : ℤ))]
    rw [hsigma, hNdef]
    nlinarith
  by_contra hcon
  push_neg at hcon
  have hcard : N.primeFactors.card ≤ 3 := by omega
  have hP := prod_le_four_mul_prod_pred
    (fun p hp => Nat.prime_of_mem_primeFactors hp) hcard
  have hQpos : 0 < ∏ p ∈ N.primeFactors, (p - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have key := sigma_mul_prod_pred_le N hN
  have h1 : (∏ p ∈ N.primeFactors, p) * N ≤ 4 * (∏ p ∈ N.primeFactors, (p - 1)) * N :=
    Nat.mul_le_mul_right _ hP
  have h2 : 4 * N * (∏ p ∈ N.primeFactors, (p - 1))
      < (∏ p ∈ N.primeFactors, (p - 1)) * σ 1 N := by
    calc 4 * N * (∏ p ∈ N.primeFactors, (p - 1))
        = (∏ p ∈ N.primeFactors, (p - 1)) * (4 * N) := by ring
      _ < (∏ p ∈ N.primeFactors, (p - 1)) * σ 1 N :=
          mul_lt_mul_of_pos_left habund hQpos
  linarith [key, h1, h2]

end BetrothedNumbers
end Brockian

