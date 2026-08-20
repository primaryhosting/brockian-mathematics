import Mathlib

namespace Brockian.OddPerfectThreePrimes

open Finset

/-- A geometric-sum identity: `(1 + p + ⋯ + p ^ a) * (p - 1) + 1 = p ^ (a + 1)`. -/

lemma sum_divisors_lt_two_mul_of_two_primes {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) :
    ∑ d ∈ (p ^ a * q ^ b).divisors, d < 2 * (p ^ a * q ^ b) := by
  have hcoprime : Nat.Coprime (p ^ a) (q ^ b) := Nat.coprime_pow_primes a b hp hq hpq
  have h₁ : ∑ d ∈ (p ^ a).divisors, d = ∑ i ∈ Finset.range (a + 1), p ^ i := by
    rw [Nat.divisors_prime_pow hp]
    simp [Finset.sum_map]
  have h₂ : ∑ d ∈ (q ^ b).divisors, d = ∑ j ∈ Finset.range (b + 1), q ^ j := by
    rw [Nat.divisors_prime_pow hq]
    simp [Finset.sum_map]
  -- Multiplicativity of sum of divisors
  have hmul : ∑ d ∈ (p ^ a * q ^ b).divisors, d =
      (∑ d ∈ (p ^ a).divisors, d) * (∑ d ∈ (q ^ b).divisors, d) := by
    rw [Nat.divisors_mul]
    simp [Finset.mul_def]
    rw [Finset.sum_image]
    · rw [Finset.sum_product]
      simp [Finset.sum_mul_sum]
    · -- Need to prove injectivity: if p^i * q^j = p^k * q^l then (i,j) = (k,l)
      intro ⟨x₁, y₁⟩ hx₁ ⟨x₂, y₂⟩ hx₂ heq
      simp only [Finset.mem_coe, Finset.mem_product] at hx₁ hx₂
      rw [Nat.mem_divisors] at hx₁ hx₂
      simp only [Nat.mem_divisors] at hx₁ hx₂
      have h1 : x₁ ∣ p ^ a := hx₁.1.1
      have h2 : y₁ ∣ q ^ b := hx₁.2.1
      have h3 : x₂ ∣ p ^ a := hx₂.1.1
      have h4 : y₂ ∣ q ^ b := hx₂.2.1
      -- Divisors of p^a are p^i for i ≤ a
      rw [Nat.dvd_prime_pow hp] at h1 h3
      rw [Nat.dvd_prime_pow hq] at h2 h4
      -- Now h1 : ∃ k ≤ a, x₁ = p ^ k, etc.
      obtain ⟨i, hi, hx₁⟩ := h1
      obtain ⟨j, hj, hy₁⟩ := h2
      obtain ⟨k, hk, hx₂⟩ := h3
      obtain ⟨l, hl, hy₂⟩ := h4
      -- heq becomes p^i * q^j = p^k * q^l
      simp only [hx₁, hy₁, hx₂, hy₂] at heq
      -- From unique factorization, i = k and j = l
      have eq1 : i = k := by
        have h := congr_arg (·.factorization p) heq
        have hqp : q.factorization p = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          right; left
          exact fun hdvd => hpq (Nat.prime_dvd_prime_iff_eq hp hq |>.mp hdvd)
        simp [Nat.factorization_mul (pow_ne_zero i hp.ne_zero) (pow_ne_zero j hq.ne_zero),
              Nat.factorization_mul (pow_ne_zero k hp.ne_zero) (pow_ne_zero l hq.ne_zero),
              hp.factorization_self, hqp] at h
        exact h
      have eq2 : j = l := by
        have h := congr_arg (·.factorization q) heq
        have hpq' : p.factorization q = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          right; left
          exact fun hdvd => hpq (Nat.prime_dvd_prime_iff_eq hq hp |>.mp hdvd).symm
        simp [Nat.factorization_mul (pow_ne_zero i hp.ne_zero) (pow_ne_zero j hq.ne_zero),
              Nat.factorization_mul (pow_ne_zero k hp.ne_zero) (pow_ne_zero l hq.ne_zero),
              hpq', hq.factorization_self] at h
        exact h
      rw [hx₁, hx₂, eq1, hy₁, hy₂, eq2]
  -- Now combine: sum = (geom sum for p) * (geom sum for q)
  rw [hmul, h₁, h₂]
  -- Use geomSum_mul_pred
  have hp_ge_1 : 1 ≤ p := hp.one_lt.le
  have hpred_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hpred_pos' : 0 < q - 1 := Nat.sub_pos_of_lt hq.one_lt
  -- From geomSum_mul_pred: geom_sum * (p-1) + 1 = p^(a+1)
  -- So geom_sum = (p^(a+1) - 1) / (p - 1) < p^(a+1) / (p - 1)
  have geom_p : (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) + 1 = p ^ (a + 1) := geomSum_mul_pred p a hp_ge_1
  have geom_q : (∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1) + 1 = q ^ (b + 1) := geomSum_mul_pred q b hq.one_lt.le
  -- Bound the geometric sums
  have Sp_bound : (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) < p ^ (a + 1) := by omega
  have Sq_bound : (∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1) < q ^ (b + 1) := by omega
  -- Use prime_pair_bound
  have ppb := prime_pair_bound hp3 hq5
  -- Sp * Sq * (p-1) * (q-1) < p^(a+1) * q^(b+1)
  have prod_bound : (∑ i ∈ Finset.range (a + 1), p ^ i) * (∑ j ∈ Finset.range (b + 1), q ^ j) * ((p - 1) * (q - 1)) < p ^ (a + 1) * q ^ (b + 1) := by
    have step1 : ((∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1)) * ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) < p ^ (a + 1) * ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) :=
      Nat.mul_lt_mul_of_pos_right Sp_bound (by positivity)
    have step2 : p ^ (a + 1) * ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) < p ^ (a + 1) * q ^ (b + 1) :=
      Nat.mul_lt_mul_of_pos_left Sq_bound (by positivity)
    calc (∑ i ∈ Finset.range (a + 1), p ^ i) * (∑ j ∈ Finset.range (b + 1), q ^ j) * ((p - 1) * (q - 1))
        = ((∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1)) * ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) := by ring
      _ < p ^ (a + 1) * ((∑ j ∈ Finset.range (b + 1), q ^ j) * (q - 1)) := step1
      _ < p ^ (a + 1) * q ^ (b + 1) := step2
  -- p^(a+1) * q^(b+1) = p^a * q^b * (p * q)
  have expand : p ^ (a + 1) * q ^ (b + 1) = p ^ a * q ^ b * (p * q) := by ring
  rw [expand] at prod_bound
  -- From ppb: p * q ≤ 2 * ((p-1)*(q-1))
  -- So prod_bound: Sp * Sq * ((p-1)*(q-1)) < p^a * q^b * (p*q) ≤ p^a * q^b * 2 * ((p-1)*(q-1))
  have upper : p ^ a * q ^ b * (p * q) ≤ 2 * (p ^ a * q ^ b) * ((p - 1) * (q - 1)) := by
    calc p ^ a * q ^ b * (p * q) ≤ p ^ a * q ^ b * (2 * ((p - 1) * (q - 1))) := Nat.mul_le_mul_left _ ppb
      _ = 2 * (p ^ a * q ^ b) * ((p - 1) * (q - 1)) := by ring
  -- Combining
  have combined : (∑ i ∈ Finset.range (a + 1), p ^ i) * (∑ j ∈ Finset.range (b + 1), q ^ j) * ((p - 1) * (q - 1)) < 2 * (p ^ a * q ^ b) * ((p - 1) * (q - 1)) := lt_of_lt_of_le prod_bound upper
  -- Divide by ((p-1)*(q-1))
  have pos_prod : 0 < (p - 1) * (q - 1) := Nat.mul_pos hpred_pos hpred_pos'
  exact Nat.lt_of_mul_lt_mul_right combined

/-- Criterion for deficiency in terms of the sum of all divisors. -/
