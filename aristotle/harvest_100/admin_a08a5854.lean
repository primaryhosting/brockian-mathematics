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

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

/-- Geometric sum identity in `ℕ`, phrased so as to avoid truncated subtraction. -/
lemma geom_sum_mul_succ (q a : ℕ) :
    (∑ i ∈ Finset.range (a + 1), (q + 1) ^ i) * q + 1 = (q + 1) ^ (a + 1) := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Finset.sum_range_succ, add_mul]
      have : (q + 1) ^ (a + 1 + 1) = (q + 1) ^ (a + 1) * q + (q + 1) ^ (a + 1) := by ring
      omega

/-- The sum of divisors of a prime power. -/
lemma sigma_prime_pow (p a : ℕ) (hp : p.Prime) :
    sigma 1 (p ^ a) = ∑ i ∈ Finset.range (a + 1), p ^ i := by
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]

/-- Key local bound: `σ(p^a) * (p-1) ≤ p^a * p`. -/
lemma sigma_prime_pow_mul_pred_le {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sigma 1 (p ^ a) * (p - 1) ≤ p ^ a * p := by
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hgs := geom_sum_mul_succ q a
  rw [sigma_prime_pow _ _ hp]
  simp only [Nat.add_sub_cancel]
  calc (∑ i ∈ Finset.range (a + 1), (q + 1) ^ i) * q
      ≤ (∑ i ∈ Finset.range (a + 1), (q + 1) ^ i) * q + 1 := Nat.le_succ _
    _ = (q + 1) ^ (a + 1) := hgs
    _ = (q + 1) ^ a * (q + 1) := by ring

/-- The global bound `σ(N) * ∏_{p ∣ N} (p-1) ≤ N * ∏_{p ∣ N} p`. -/
lemma sigma_mul_prod_pred_le {N : ℕ} (hN : N ≠ 0) :
    sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1) ≤ N * ∏ p ∈ N.primeFactors, p := by
  have hsig : sigma 1 N = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hN]
    rfl
  have hN' : N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rfl
  have h1 : sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1)
      = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) * (p - 1) := by
    rw [hsig, ← Finset.prod_mul_distrib]
  have h2 : ∏ p ∈ N.primeFactors, p ^ N.factorization p * p
      = N * ∏ p ∈ N.primeFactors, p := by
    rw [Finset.prod_mul_distrib, ← hN']
  calc sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1)
      = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) * (p - 1) := h1
    _ ≤ ∏ p ∈ N.primeFactors, p ^ N.factorization p * p := by
        refine Finset.prod_le_prod' ?_
        intro p hp
        exact sigma_prime_pow_mul_pred_le (Nat.prime_of_mem_primeFactors hp) _
    _ = N * ∏ p ∈ N.primeFactors, p := h2

/-- Three distinct primes in increasing order satisfy `4 p q r ≤ 15 (p-1)(q-1)(r-1)`. -/
lemma four_mul_le_fifteen_mul_three {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) :
    4 * (p * q * r) ≤ 15 * ((p - 1) * ((q - 1) * (r - 1))) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq3 : 3 ≤ q := by omega
  have hr5 : 5 ≤ r := by
    have h4 : r ≠ 4 := by rintro rfl; norm_num at hr
    omega
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  nlinarith [hp2, hq3, hr5, Nat.zero_le (p' * q'), Nat.zero_le (q' * r'), Nat.zero_le (p' * r'),
    Nat.zero_le (p' * q' * r')]

/-- For a set of at most three primes, `4 ∏ p ≤ 15 ∏ (p-1)`. -/
lemma prod_bound_of_card_le_three {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 3) :
    4 * ∏ p ∈ S, p ≤ 15 * ∏ p ∈ S, (p - 1) := by
  interval_cases h : S.card
  · rw [Finset.card_eq_zero] at h
    subst h; simp
  · rw [Finset.card_eq_one] at h
    obtain ⟨a, rfl⟩ := h
    have ha : a.Prime := hS a (by simp)
    have := ha.two_le
    simp only [Finset.prod_singleton]
    omega
  · rw [Finset.card_eq_two] at h
    obtain ⟨a, b, hab, rfl⟩ := h
    have ha : a.Prime := hS a (by simp)
    have hb : b.Prime := hS b (by simp)
    -- wlog a < b
    have key : ∀ x y : ℕ, x.Prime → y.Prime → x < y →
        4 * (x * y) ≤ 15 * ((x - 1) * (y - 1)) := by
      intro x y hx hy hxy
      have hx2 : 2 ≤ x := hx.two_le
      have hy3 : 3 ≤ y := by omega
      obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
      obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith [hx2, hy3, Nat.zero_le (x' * y')]
    rw [Finset.prod_pair hab, Finset.prod_pair hab]
    rcases lt_or_gt_of_ne hab with h1 | h1
    · exact key a b ha hb h1
    · have := key b a hb ha h1
      calc 4 * (a * b) = 4 * (b * a) := by ring
        _ ≤ 15 * ((b - 1) * (a - 1)) := this
        _ = 15 * ((a - 1) * (b - 1)) := by ring
  · rw [Finset.card_eq_three] at h
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := h
    have ha : a.Prime := hS a (by simp)
    have hb : b.Prime := hS b (by simp)
    have hc : c.Prime := hS c (by simp)
    have hprod : ∀ x y z : ℕ, x ≠ y → x ≠ z → y ≠ z →
        ∏ p ∈ ({x, y, z} : Finset ℕ), p = x * (y * z) := by
      intro x y z h1 h2 h3
      rw [Finset.prod_insert (by simp [h1, h2]), Finset.prod_pair h3]
    have hprod' : ∀ x y z : ℕ, x ≠ y → x ≠ z → y ≠ z →
        ∏ p ∈ ({x, y, z} : Finset ℕ), (p - 1) = (x - 1) * ((y - 1) * (z - 1)) := by
      intro x y z h1 h2 h3
      rw [Finset.prod_insert (by simp [h1, h2]), Finset.prod_pair h3]
    have key : ∀ x y z : ℕ, x.Prime → y.Prime → z.Prime → x < y → y < z →
        4 * (x * (y * z)) ≤ 15 * ((x - 1) * ((y - 1) * (z - 1))) := by
      intro x y z hx hy hz h1 h2
      have := four_mul_le_fifteen_mul_three hx hy hz h1 h2
      calc 4 * (x * (y * z)) = 4 * (x * y * z) := by ring
        _ ≤ 15 * ((x - 1) * ((y - 1) * (z - 1))) := this
    -- sort a b c
    have main : ∀ x y z : ℕ, x.Prime → y.Prime → z.Prime → x ≠ y → x ≠ z → y ≠ z →
        4 * ∏ p ∈ ({x, y, z} : Finset ℕ), p ≤ 15 * ∏ p ∈ ({x, y, z} : Finset ℕ), (p - 1) := by
      intro x y z hx hy hz h1 h2 h3
      rw [hprod x y z h1 h2 h3, hprod' x y z h1 h2 h3]
      rcases lt_trichotomy x y with hxy | hxy | hxy
      · rcases lt_trichotomy y z with hyz | hyz | hyz
        · exact key x y z hx hy hz hxy hyz
        · exact absurd hyz h3
        · rcases lt_trichotomy x z with hxz | hxz | hxz
          · have := key x z y hx hz hy hxz hyz
            calc 4 * (x * (y * z)) = 4 * (x * (z * y)) := by ring
              _ ≤ 15 * ((x - 1) * ((z - 1) * (y - 1))) := this
              _ = 15 * ((x - 1) * ((y - 1) * (z - 1))) := by ring
          · exact absurd hxz h2
          · have := key z x y hz hx hy hxz hxy
            calc 4 * (x * (y * z)) = 4 * (z * (x * y)) := by ring
              _ ≤ 15 * ((z - 1) * ((x - 1) * (y - 1))) := this
              _ = 15 * ((x - 1) * ((y - 1) * (z - 1))) := by ring
      · exact absurd hxy h1
      · rcases lt_trichotomy x z with hxz | hxz | hxz
        · have := key y x z hy hx hz hxy hxz
          calc 4 * (x * (y * z)) = 4 * (y * (x * z)) := by ring
            _ ≤ 15 * ((y - 1) * ((x - 1) * (z - 1))) := this
            _ = 15 * ((x - 1) * ((y - 1) * (z - 1))) := by ring
        · exact absurd hxz h2
        · rcases lt_trichotomy y z with hyz | hyz | hyz
          · have := key y z x hy hz hx hyz hxz
            calc 4 * (x * (y * z)) = 4 * (y * (z * x)) := by ring
              _ ≤ 15 * ((y - 1) * ((z - 1) * (x - 1))) := this
              _ = 15 * ((x - 1) * ((y - 1) * (z - 1))) := by ring
          · exact absurd hyz h3
          · have := key z y x hz hy hx hyz hxy
            calc 4 * (x * (y * z)) = 4 * (z * (y * x)) := by ring
              _ ≤ 15 * ((z - 1) * ((y - 1) * (x - 1))) := this
              _ = 15 * ((x - 1) * ((y - 1) * (z - 1))) := by ring
    exact main a b c ha hb hc hab hac hbc

/-- If a positive integer has at most three distinct prime factors then it is not
`4`-abundant: `σ(N) < 4N`. -/
lemma sigma_lt_four_mul_of_card_le_three {N : ℕ} (hN : N ≠ 0)
    (hcard : N.primeFactors.card ≤ 3) : sigma 1 N < 4 * N := by
  have h1 := sigma_mul_prod_pred_le hN
  have h2 : 4 * ∏ p ∈ N.primeFactors, p ≤ 15 * ∏ p ∈ N.primeFactors, (p - 1) :=
    prod_bound_of_card_le_three (fun p hp => Nat.prime_of_mem_primeFactors hp) hcard
  have hpos : 0 < ∏ p ∈ N.primeFactors, (p - 1) := by
    refine Finset.prod_pos ?_
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have h3 : 4 * (sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1)) ≤ N * (4 * ∏ p ∈ N.primeFactors, p) := by
    calc 4 * (sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1))
        ≤ 4 * (N * ∏ p ∈ N.primeFactors, p) := by exact Nat.mul_le_mul_left _ h1
      _ = N * (4 * ∏ p ∈ N.primeFactors, p) := by ring
  have h4 : N * (4 * ∏ p ∈ N.primeFactors, p) ≤ N * (15 * ∏ p ∈ N.primeFactors, (p - 1)) :=
    Nat.mul_le_mul_left _ h2
  have h5 : (4 * sigma 1 N) * (∏ p ∈ N.primeFactors, (p - 1))
      ≤ (15 * N) * (∏ p ∈ N.primeFactors, (p - 1)) := by
    calc (4 * sigma 1 N) * (∏ p ∈ N.primeFactors, (p - 1))
        = 4 * (sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1)) := by ring
      _ ≤ N * (15 * ∏ p ∈ N.primeFactors, (p - 1)) := le_trans h3 h4
      _ = (15 * N) * (∏ p ∈ N.primeFactors, (p - 1)) := by ring
  have h6 : 4 * sigma 1 N ≤ 15 * N := Nat.le_of_mul_le_mul_right h5 hpos
  omega

/-- `m` and `n` are *betrothed* (quasi-amicable) numbers: they are distinct and each has
divisor sum equal to `m + n + 1`. -/
def Betrothed (m n : ℕ) : Prop :=
  m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- Betrothed numbers are positive. -/
lemma Betrothed.pos_left {m n : ℕ} (h : Betrothed m n) : 0 < m := by
  rcases h with ⟨-, hm, -⟩
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp [ArithmeticFunction.map_zero] at hm
  · exact hpos

/-- Betrothed numbers are positive. -/
lemma Betrothed.pos_right {m n : ℕ} (h : Betrothed m n) : 0 < n := by
  rcases h with ⟨-, -, hn⟩
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [ArithmeticFunction.map_zero] at hn
  · exact hpos

/-- The notion is not vacuous: `(48, 75)` is the smallest betrothed pair.
(It is of course not a coprime pair: `gcd 48 75 = 3`.) -/
example : Betrothed 48 75 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> decide

/-- **Hagis–Lord, Proposition 2.** If `m` and `n` are coprime betrothed numbers, then
`m * n` has at least four distinct prime factors. -/
theorem coprime_pair_four_primeFactors {m n : ℕ} (h : Betrothed m n)
    (hco : Nat.Coprime m n) : 4 ≤ (m * n).primeFactors.card := by
  have hmpos : 0 < m := h.pos_left
  have hnpos : 0 < n := h.pos_right
  obtain ⟨-, hm, hn⟩ := h
  by_contra hcon
  push_neg at hcon
  have hcard : (m * n).primeFactors.card ≤ 3 := by omega
  have hne : m * n ≠ 0 := by positivity
  have hlt := sigma_lt_four_mul_of_card_le_three hne hcard
  have hmul : sigma 1 (m * n) = sigma 1 m * sigma 1 n := isMultiplicative_sigma.map_mul_of_coprime hco
  rw [hmul, hm, hn] at hlt
  -- but `(m+n+1)^2 > 4mn`
  have hkey : 4 * (m * n) < (m + n + 1) * (m + n + 1) := by
    zify
    nlinarith [sq_nonneg ((m : ℤ) - (n : ℤ)), hmpos, hnpos]
  omega

end BetrothedNumbers
end Brockian

