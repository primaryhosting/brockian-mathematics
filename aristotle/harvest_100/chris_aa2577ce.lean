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

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, distinct, and
the sum of the divisors of each equals `m + n + 1`. -/
def IsBetrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- The geometric-sum identity `(1 + p + ⋯ + p ^ k) * (p - 1) + 1 = p ^ (k + 1)`. -/
lemma geom_sum_mul_pred (p k : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ Finset.range (k + 1), p ^ i) * (p - 1) + 1 = p ^ (k + 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_mul, add_assoc, add_comm (((q + 1) ^ (k + 1)) * ((q + 1) - 1)) 1,
      ← add_assoc, ih]
    simp only [Nat.add_sub_cancel]
    ring

/-- For a prime power, `σ(p ^ k) * (p - 1) ≤ p ^ k * p`. -/
lemma sigma_primePow_mul_pred_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sigma 1 (p ^ k) * (p - 1) ≤ p ^ k * p := by
  have h1 : sigma 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
    rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  rw [h1]
  have h2 := geom_sum_mul_pred p k hp.one_lt.le
  have h3 : p ^ k * p = p ^ (k + 1) := by ring
  omega

/-- The abundancy bound `σ(N) * ∏_{p ∣ N} (p - 1) ≤ N * ∏_{p ∣ N} p`, obtained from the
multiplicativity of `σ` and the corresponding bound at each prime power. -/
lemma sigma_mul_prod_pred_le {N : ℕ} (hN : N ≠ 0) :
    sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1) ≤ N * ∏ p ∈ N.primeFactors, p := by
  have hs : sigma 1 N = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hN]
    rfl
  have hn : ∏ p ∈ N.primeFactors, p ^ N.factorization p = N := by
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rfl
  calc sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1)
      = ∏ p ∈ N.primeFactors, (sigma 1 (p ^ N.factorization p) * (p - 1)) := by
        rw [hs, Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ N.primeFactors, (p ^ N.factorization p * p) := by
        refine Finset.prod_le_prod' ?_
        intro p hp
        exact sigma_primePow_mul_pred_le (Nat.prime_of_mem_primeFactors hp) _
    _ = N * ∏ p ∈ N.primeFactors, p := by rw [Finset.prod_mul_distrib, hn]

/-- Two distinct increasing primes satisfy `4ab ≤ 15 (a-1)(b-1)`. -/
lemma four_mul_prod_two_le {a b : ℕ} (ha : a.Prime) (hab : a < b) :
    4 * (a * b) ≤ 15 * ((a - 1) * (b - 1)) := by
  have ha2 : 2 ≤ a := ha.two_le
  have hb3 : 3 ≤ b := by omega
  obtain ⟨x, rfl⟩ : ∃ x, a = x + 2 := ⟨a - 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = y + 3 := ⟨b - 3, by omega⟩
  have e1 : x + 2 - 1 = x + 1 := by omega
  have e2 : y + 3 - 1 = y + 2 := by omega
  rw [e1, e2]
  nlinarith [Nat.zero_le x, Nat.zero_le y, Nat.zero_le (x * y)]

/-- Symmetric version of `four_mul_prod_two_le`. -/
lemma four_mul_prod_two_le' {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b) :
    4 * (a * b) ≤ 15 * ((a - 1) * (b - 1)) := by
  rcases Nat.lt_or_ge a b with h | h
  · exact four_mul_prod_two_le ha h
  · have h : b < a := lt_of_le_of_ne h (Ne.symm hab)
    have hba := four_mul_prod_two_le hb h
    calc 4 * (a * b) = 4 * (b * a) := by ring
      _ ≤ 15 * ((b - 1) * (a - 1)) := hba
      _ = 15 * ((a - 1) * (b - 1)) := by ring

/-- Three increasing primes satisfy `4abc ≤ 15 (a-1)(b-1)(c-1)`; the extremal case is
`(a, b, c) = (2, 3, 5)`, where both sides equal `120`. -/
lemma four_mul_prod_three_le {a b c : ℕ} (ha : a.Prime) (hc : c.Prime)
    (hab : a < b) (hbc : b < c) :
    4 * (a * b * c) ≤ 15 * ((a - 1) * (b - 1) * (c - 1)) := by
  have ha2 : 2 ≤ a := ha.two_le
  have hb3 : 3 ≤ b := by omega
  have hc5 : 5 ≤ c := by
    have h4 : c ≠ 4 := by rintro rfl; norm_num at hc
    omega
  obtain ⟨x, rfl⟩ : ∃ x, a = x + 2 := ⟨a - 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = y + 3 := ⟨b - 3, by omega⟩
  obtain ⟨z, rfl⟩ : ∃ z, c = z + 5 := ⟨c - 5, by omega⟩
  have e1 : x + 2 - 1 = x + 1 := by omega
  have e2 : y + 3 - 1 = y + 2 := by omega
  have e3 : z + 5 - 1 = z + 4 := by omega
  rw [e1, e2, e3]
  nlinarith [Nat.zero_le x, Nat.zero_le y, Nat.zero_le z, Nat.zero_le (x * y),
    Nat.zero_le (y * z), Nat.zero_le (x * z), Nat.zero_le (x * y * z)]

/-- Symmetric version of `four_mul_prod_three_le`. -/
lemma four_mul_prod_three_le' {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    4 * (a * b * c) ≤ 15 * ((a - 1) * (b - 1) * (c - 1)) := by
  rcases Nat.lt_or_ge a b with h1 | h1
  · rcases Nat.lt_or_ge b c with h2 | h2
    · exact four_mul_prod_three_le ha hc h1 h2
    · have h2 : c < b := lt_of_le_of_ne h2 (Ne.symm hbc)
      rcases Nat.lt_or_ge a c with h3 | h3
      · have hacb := four_mul_prod_three_le ha hb h3 h2
        calc 4 * (a * b * c) = 4 * (a * c * b) := by ring
          _ ≤ 15 * ((a - 1) * (c - 1) * (b - 1)) := hacb
          _ = 15 * ((a - 1) * (b - 1) * (c - 1)) := by ring
      · have h3 : c < a := lt_of_le_of_ne h3 (Ne.symm hac)
        have hcab := four_mul_prod_three_le hc hb h3 h1
        calc 4 * (a * b * c) = 4 * (c * a * b) := by ring
          _ ≤ 15 * ((c - 1) * (a - 1) * (b - 1)) := hcab
          _ = 15 * ((a - 1) * (b - 1) * (c - 1)) := by ring
  · have h1 : b < a := lt_of_le_of_ne h1 (Ne.symm hab)
    rcases Nat.lt_or_ge a c with h2 | h2
    · have hbac := four_mul_prod_three_le hb hc h1 h2
      calc 4 * (a * b * c) = 4 * (b * a * c) := by ring
        _ ≤ 15 * ((b - 1) * (a - 1) * (c - 1)) := hbac
        _ = 15 * ((a - 1) * (b - 1) * (c - 1)) := by ring
    · have h2 : c < a := lt_of_le_of_ne h2 (Ne.symm hac)
      rcases Nat.lt_or_ge b c with h3 | h3
      · have hbca := four_mul_prod_three_le hb ha h3 h2
        calc 4 * (a * b * c) = 4 * (b * c * a) := by ring
          _ ≤ 15 * ((b - 1) * (c - 1) * (a - 1)) := hbca
          _ = 15 * ((a - 1) * (b - 1) * (c - 1)) := by ring
      · have h3 : c < b := lt_of_le_of_ne h3 (Ne.symm hbc)
        have hcba := four_mul_prod_three_le hc ha h3 h1
        calc 4 * (a * b * c) = 4 * (c * b * a) := by ring
          _ ≤ 15 * ((c - 1) * (b - 1) * (a - 1)) := hcba
          _ = 15 * ((a - 1) * (b - 1) * (c - 1)) := by ring

/-- For a set of at most three primes, `4 ∏ p ≤ 15 ∏ (p - 1)`; equivalently
`∏ p / (p - 1) ≤ 15 / 4 < 4`. -/
lemma four_mul_prod_le_of_card_le_three {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hcard : S.card ≤ 3) :
    4 * ∏ p ∈ S, p ≤ 15 * ∏ p ∈ S, (p - 1) := by
  rcases (by omega : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3) with h | h | h | h
  · rw [Finset.card_eq_zero] at h
    subst h
    simp
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    have ha : a.Prime := hS a (by simp)
    have ha2 := ha.two_le
    simp only [Finset.prod_singleton]
    omega
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    have ha : a.Prime := hS a (by simp)
    have hb : b.Prime := hS b (by simp)
    rw [Finset.prod_pair hab, Finset.prod_pair hab]
    exact four_mul_prod_two_le' ha hb hab
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h
    have ha : a.Prime := hS a (by simp)
    have hb : b.Prime := hS b (by simp)
    have hc : c.Prime := hS c (by simp)
    have habc := four_mul_prod_three_le' ha hb hc hab hac hbc
    rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc,
      Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc]
    calc 4 * (a * (b * c)) = 4 * (a * b * c) := by ring
      _ ≤ 15 * ((a - 1) * (b - 1) * (c - 1)) := habc
      _ = 15 * ((a - 1) * ((b - 1) * (c - 1))) := by ring

/-- If `N` has at most three distinct prime factors then `σ(N) / N ≤ 15 / 4`. -/
lemma four_mul_sigma_le_of_card_le_three {N : ℕ} (hN : N ≠ 0)
    (hcard : N.primeFactors.card ≤ 3) :
    4 * sigma 1 N ≤ 15 * N := by
  set P := ∏ p ∈ N.primeFactors, p with hP
  set P' := ∏ p ∈ N.primeFactors, (p - 1) with hP'
  have hP'pos : 0 < P' := by
    rw [hP']
    refine Finset.prod_pos ?_
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have h1 : sigma 1 N * P' ≤ N * P := sigma_mul_prod_pred_le hN
  have h2 : 4 * P ≤ 15 * P' :=
    four_mul_prod_le_of_card_le_three (fun p hp => Nat.prime_of_mem_primeFactors hp) hcard
  have h3 : (4 * sigma 1 N) * P' ≤ (15 * N) * P' := by
    calc (4 * sigma 1 N) * P' = 4 * (sigma 1 N * P') := by ring
      _ ≤ 4 * (N * P) := Nat.mul_le_mul_left 4 h1
      _ = N * (4 * P) := by ring
      _ ≤ N * (15 * P') := Nat.mul_le_mul_left N h2
      _ = (15 * N) * P' := by ring
  exact Nat.le_of_mul_le_mul_right h3 hP'pos

/-- **Hagis–Lord, Proposition 2.** If `m` and `n` are coprime betrothed numbers, then `m * n`
has at least four distinct prime factors.

Indeed `σ(mn) = σ(m)σ(n) = (m + n + 1)^2 > 4mn` by multiplicativity of `σ` and AM–GM, while a
number with at most three distinct prime factors satisfies `σ(N) ≤ (15/4) N < 4N`. -/
theorem coprime_pair_four_primeFactors {m n : ℕ} (h : IsBetrothed m n)
    (hcop : Nat.Coprime m n) :
    4 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn, _hne, hsm, hsn⟩ := h
  by_contra hcon
  push_neg at hcon
  have hcard : (m * n).primeFactors.card ≤ 3 := by omega
  have hN : m * n ≠ 0 := Nat.mul_ne_zero hm.ne' hn.ne'
  have hsig : sigma 1 (m * n) = (m + n + 1) * (m + n + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, hsm, hsn]
  have hkey : 4 * sigma 1 (m * n) ≤ 15 * (m * n) := four_mul_sigma_le_of_card_le_three hN hcard
  rw [hsig] at hkey
  have hgt : 4 * (m * n) < (m + n + 1) * (m + n + 1) := by
    zify
    nlinarith [sq_nonneg ((m : ℤ) - n), (by exact_mod_cast hm : (0:ℤ) < m),
      (by exact_mod_cast hn : (0:ℤ) < n)]
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  omega

/-- The definition is not vacuous: `(48, 75)` is the smallest betrothed pair.  (It is not a
*coprime* pair — `gcd 48 75 = 3` — and indeed no coprime betrothed pair is known.) -/
example : IsBetrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;>
    · simp [sigma_one_apply]
      decide

end Brockian.BetrothedNumbers

