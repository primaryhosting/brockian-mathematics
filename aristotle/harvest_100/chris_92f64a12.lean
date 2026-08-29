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

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction Finset

/-- `Betrothed m n` says that `m` and `n` are *betrothed* (quasi-amicable) numbers:
both are positive and each one's sum of divisors equals `m + n + 1`. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ (sigma 1) m = m + n + 1 ∧ (sigma 1) n = m + n + 1

/-- Sanity check that the definition is non-degenerate: `(48, 75)` is the smallest
betrothed pair (`σ 48 = σ 75 = 124 = 48 + 75 + 1`).  It is not coprime. -/
example : Betrothed 48 75 := ⟨by norm_num, by norm_num, by decide, by decide⟩

/-- Geometric sum identity: `(1 + p + ⋯ + p ^ k) * (p - 1) + 1 = p ^ (k + 1)` for `p ≥ 1`. -/
lemma geom_sum_mul_pred (p : ℕ) (hp : 1 ≤ p) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), p ^ i) * (p - 1) + 1 = p ^ (k + 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      set A := ∑ i ∈ Finset.range (k + 1), (q + 1) ^ i with hA
      set P := (q + 1) ^ (k + 1) with hP
      calc (A + P) * q + 1 = (A * q + 1) + P * q := by ring
        _ = P + P * q := by rw [ih]
        _ = (q + 1) ^ (k + 1 + 1) := by rw [hP]; ring

/-- Prime-power abundancy bound: `σ(p ^ k) * (p - 1) ≤ p ^ k * p`. -/
lemma sigma_primePow_mul_pred_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (sigma 1) (p ^ k) * (p - 1) ≤ p ^ k * p := by
  have hsum : (sigma 1) (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  rw [hsum]
  have := geom_sum_mul_pred p hp.one_lt.le k
  have hpk : p ^ (k + 1) = p ^ k * p := by ring
  omega

/-- The key abundancy bound: `σ(N) * ∏_{p ∣ N} (p - 1) ≤ N * ∏_{p ∣ N} p`. -/
lemma sigma_mul_prod_pred_le {N : ℕ} (hN : N ≠ 0) :
    (sigma 1) N * ∏ p ∈ N.primeFactors, (p - 1) ≤ N * ∏ p ∈ N.primeFactors, p := by
  have hsig : (sigma 1) N = ∏ p ∈ N.primeFactors, (sigma 1) (p ^ N.factorization p) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hN]
    rw [Finsupp.prod, Nat.support_factorization]
  have hNfac : N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rw [Finsupp.prod, Nat.support_factorization]
  calc (sigma 1) N * ∏ p ∈ N.primeFactors, (p - 1)
      = ∏ p ∈ N.primeFactors, ((sigma 1) (p ^ N.factorization p) * (p - 1)) := by
        rw [hsig, ← Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ N.primeFactors, (p ^ N.factorization p * p) := by
        refine Finset.prod_le_prod' ?_
        intro p hp
        exact sigma_primePow_mul_pred_le (Nat.prime_of_mem_primeFactors hp) _
    _ = N * ∏ p ∈ N.primeFactors, p := by
        rw [Finset.prod_mul_distrib, ← hNfac]

/-- Numeric core: `(A+1)(B+1)(C+1) ≤ 4·A·B·C` for `A ≥ 1`, `B ≥ 2`, `C ≥ 4`
(i.e. `2/1 · 3/2 · 5/4 = 15/4 ≤ 4`). -/
lemma succ_prod_le_four_mul (A B C : ℕ) (hA : 1 ≤ A) (hB : 2 ≤ B) (hC : 4 ≤ C) :
    (A + 1) * (B + 1) * (C + 1) ≤ 4 * (A * B * C) := by
  obtain ⟨a, rfl⟩ : ∃ a, A = a + 1 := ⟨A - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, B = b + 2 := ⟨B - 2, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, C = c + 4 := ⟨C - 4, by omega⟩
  nlinarith [Nat.zero_le (a * b * c), Nat.zero_le (a * b), Nat.zero_le (a * c),
    Nat.zero_le (b * c)]

/-- Three increasing primes: `a * b * c ≤ 4 * ((a-1) * (b-1) * (c-1))`. -/
lemma three_primes_sorted {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a < b) (hbc : b < c) :
    a * b * c ≤ 4 * ((a - 1) * (b - 1) * (c - 1)) := by
  have ha2 : 2 ≤ a := ha.two_le
  have hb3 : 3 ≤ b := by omega
  have hc5 : 5 ≤ c := by
    have h4 : c ≠ 4 := by rintro rfl; norm_num at hc
    omega
  obtain ⟨A, rfl⟩ : ∃ A, a = A + 1 := ⟨a - 1, by omega⟩
  obtain ⟨B, rfl⟩ : ∃ B, b = B + 1 := ⟨b - 1, by omega⟩
  obtain ⟨C, rfl⟩ : ∃ C, c = C + 1 := ⟨c - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact succ_prod_le_four_mul A B C (by omega) (by omega) (by omega)

/-- Three distinct primes: `a * b * c ≤ 4 * ((a-1) * (b-1) * (c-1))`. -/
lemma three_primes_distinct {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    a * b * c ≤ 4 * ((a - 1) * (b - 1) * (c - 1)) := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · rcases lt_trichotomy b c with h2 | h2 | h2
    · linarith [three_primes_sorted ha hb hc h1 h2]
    · exact absurd h2 hbc
    · rcases lt_trichotomy a c with h3 | h3 | h3
      · linarith [three_primes_sorted ha hc hb h3 h2]
      · exact absurd h3 hac
      · linarith [three_primes_sorted hc ha hb h3 h1]
  · exact absurd h1 hab
  · rcases lt_trichotomy a c with h2 | h2 | h2
    · linarith [three_primes_sorted hb ha hc h1 h2]
    · exact absurd h2 hac
    · rcases lt_trichotomy b c with h3 | h3 | h3
      · linarith [three_primes_sorted hb hc ha h3 h2]
      · exact absurd h3 hbc
      · linarith [three_primes_sorted hc hb ha h3 h1]

/-- For a set of at most three primes, `∏ p ≤ 4 * ∏ (p - 1)`. -/
lemma prod_le_four_mul_prod_pred {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (h3 : P.card ≤ 3) :
    ∏ p ∈ P, p ≤ 4 * ∏ p ∈ P, (p - 1) := by
  rcases lt_or_ge P.card 3 with hlt | hge
  · -- crude bound `p ≤ 2 * (p - 1)`, giving `∏ p ≤ 2 ^ card * ∏ (p - 1) ≤ 4 * ∏ (p - 1)`
    have hstep : ∏ p ∈ P, p ≤ ∏ p ∈ P, (2 * (p - 1)) := by
      refine Finset.prod_le_prod' ?_
      intro p hp
      have := (hP p hp).two_le
      omega
    have hsplit : ∏ p ∈ P, (2 * (p - 1)) = 2 ^ P.card * ∏ p ∈ P, (p - 1) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    have hpow : (2:ℕ) ^ P.card ≤ 4 := by
      calc (2:ℕ) ^ P.card ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    calc ∏ p ∈ P, p ≤ 2 ^ P.card * ∏ p ∈ P, (p - 1) := by rw [← hsplit]; exact hstep
      _ ≤ 4 * ∏ p ∈ P, (p - 1) := Nat.mul_le_mul_right _ hpow
  · have hc : P.card = 3 := le_antisymm h3 hge
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hc
    have ha : a.Prime := hP a (by simp)
    have hb : b.Prime := hP b (by simp)
    have hcp : c.Prime := hP c (by simp)
    have h1 : ∏ p ∈ ({a, b, c} : Finset ℕ), p = a * b * c := by
      rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
        Finset.prod_singleton, ← mul_assoc]
    have h2 : ∏ p ∈ ({a, b, c} : Finset ℕ), (p - 1) = (a - 1) * ((b - 1) * (c - 1)) := by
      rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
        Finset.prod_singleton]
    rw [h1, h2, ← mul_assoc (a - 1) (b - 1) (c - 1)]
    exact three_primes_distinct ha hb hcp hab hac hbc

/-- If `σ(N) > 4N` then `N` has at least four distinct prime factors. -/
lemma four_le_card_primeFactors_of_abundancy {N : ℕ} (hN : N ≠ 0) (h : 4 * N < (sigma 1) N) :
    4 ≤ N.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have h3 : N.primeFactors.card ≤ 3 := by omega
  have hprimes : ∀ p ∈ N.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < ∏ p ∈ N.primeFactors, (p - 1) := by
    refine Finset.prod_pos ?_
    intro p hp
    have := (hprimes p hp).two_le
    omega
  have hA := sigma_mul_prod_pred_le hN
  have hB := prod_le_four_mul_prod_pred hprimes h3
  have hC : N * ∏ p ∈ N.primeFactors, p ≤ N * (4 * ∏ p ∈ N.primeFactors, (p - 1)) :=
    Nat.mul_le_mul_left _ hB
  have hD : (sigma 1) N * ∏ p ∈ N.primeFactors, (p - 1)
      ≤ (4 * N) * ∏ p ∈ N.primeFactors, (p - 1) := by
    calc (sigma 1) N * ∏ p ∈ N.primeFactors, (p - 1)
        ≤ N * (4 * ∏ p ∈ N.primeFactors, (p - 1)) := le_trans hA hC
      _ = (4 * N) * ∏ p ∈ N.primeFactors, (p - 1) := by ring
  have := Nat.le_of_mul_le_mul_right hD hpos
  omega

/-- Hagis–Lord, Proposition 2: if `m` and `n` are coprime betrothed numbers, then `m * n`
has at least four distinct prime factors. -/
theorem coprime_pair_four_primeFactors {m n : ℕ} (h : Betrothed m n)
    (hmn : Nat.Coprime m n) : 4 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn, hsm, hsn⟩ := h
  have hN : m * n ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hmul : (sigma 1) (m * n) = (m + n + 1) * (m + n + 1) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hmn, hsm, hsn]
  have habund : 4 * (m * n) < (sigma 1) (m * n) := by
    rw [hmul]
    have hz : (4 : ℤ) * (m * n) < ((m : ℤ) + n + 1) * ((m : ℤ) + n + 1) := by
      have h1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
      have h2 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      nlinarith [sq_nonneg ((m : ℤ) - n)]
    exact_mod_cast hz
  exact four_le_card_primeFactors_of_abundancy hN habund

end BetrothedNumbers
end Brockian

