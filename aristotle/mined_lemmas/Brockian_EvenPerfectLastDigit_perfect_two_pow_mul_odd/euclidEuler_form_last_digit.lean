import Mathlib

namespace Brockian.EvenPerfectLastDigit

/-- The core of the Euclid--Euler argument.  If the exact power of two in a
perfect number is `2^k`, its odd part is the corresponding Mersenne prime. -/

theorem euclidEuler_form_last_digit {p : ℕ} (hprime : Nat.Prime (2 ^ p - 1)) :
    (2 ^ (p - 1) * (2 ^ p - 1)) % 10 = 6 ∨
      (2 ^ (p - 1) * (2 ^ p - 1)) % 10 = 8 := by
  by_cases hp2 : p = 2
  · simp [hp2]
  · -- p ≥ 2 since 2^p - 1 is prime
    have hp_pos : 2 ≤ p := by
      by_contra h
      push_neg at h
      interval_cases p <;> simp_all [Nat.Prime]
    -- If p is even, 2^p - 1 is composite (since 2^p - 1 = (2^(p/2) - 1)(2^(p/2) + 1))
    have hp_odd : Odd p := by
      by_contra hp_even
      rw [Nat.not_odd_iff_even] at hp_even
      obtain ⟨k, hk⟩ := hp_even
      have hk_pos : k ≥ 2 := by omega
      -- 2^p - 1 = 2^(2k) - 1 = (2^k - 1)(2^k + 1)
      have hfactor : 2 ^ p - 1 = (2 ^ k - 1) * (2 ^ k + 1) := by
        rw [hk]
        have h1 : k + k = k * 2 := by ring
        rw [h1, pow_mul]
        have h2 : (2 ^ k) ^ 2 - 1 = (2 ^ k - 1) * (2 ^ k + 1) := by
          have : (2 ^ k) ^ 2 - 1 = (2 ^ k) ^ 2 - 1^2 := by norm_num
          rw [this, Nat.sq_sub_sq, mul_comm]
        exact h2
      have h1 : 1 < 2 ^ k - 1 := by
        have h4 : 2 ^ k ≥ 4 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hk_pos
        omega
      have h2 : 1 < 2 ^ k + 1 := by omega
      rw [hfactor] at hprime
      exact Nat.not_prime_mul h1.ne' h2.ne' hprime
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
      rcases hp_odd with ⟨m, hm⟩
      omega
    -- Since 2^p - 1 is prime, p ≠ 1
    have hp_ne_1 : p ≠ 1 := by
      intro hp1
      rw [hp1] at hprime
      norm_num at hprime
    -- For p % 4 = 1, we have p ≥ 5
    have hp5 : p % 4 = 1 → 5 ≤ p := by intro h; omega
    -- For p % 4 = 3, we have p ≥ 3
    have hp3 : p % 4 = 3 → 3 ≤ p := by intro h; omega
    -- Helper cycles
    have hcycle1 : ∀ k : ℕ, (2 ^ (4 * k + 1)) % 10 = 2 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have : 4 * (k + 1) + 1 = 4 * k + 1 + 4 := by ring
        rw [this, pow_add]
        calc (2 ^ (4 * k + 1) * 2 ^ 4) % 10 = (2 ^ (4 * k + 1) % 10 * (2 ^ 4 % 10)) % 10 := by rw [Nat.mul_mod]
          _ = (2 * 6) % 10 := by rw [ih]; norm_num
          _ = 2 := by norm_num
    have hcycle0 : ∀ k : ℕ, k ≥ 1 → (2 ^ (4 * k)) % 10 = 6 := by
      intro k hk
      have heq : 4 * k = 4 * (k - 1) + 1 + 3 := by omega
      rw [heq]
      rw [show (4 : ℕ) * (k - 1) + 1 + 3 = (4 * (k - 1) + 1) + 3 by ring]
      rw [pow_add]
      rw [Nat.mul_mod, hcycle1 (k - 1)]
      norm_num
    have hcycle2 : ∀ k : ℕ, (2 ^ (4 * k + 2)) % 10 = 4 := by
      intro k
      have : 4 * k + 2 = 4 * k + 1 + 1 := by ring
      rw [this, pow_add]
      calc (2 ^ (4 * k + 1) * 2 ^ 1) % 10 = (2 ^ (4 * k + 1) % 10 * (2 ^ 1 % 10)) % 10 := by rw [Nat.mul_mod]
        _ = (2 * 2) % 10 := by rw [hcycle1 k]; norm_num
        _ = 4 := by norm_num
    have hcycle3 : ∀ k : ℕ, (2 ^ (4 * k + 3)) % 10 = 8 := by
      intro k
      have : 4 * k + 3 = 4 * k + 2 + 1 := by ring
      rw [this, pow_add]
      calc (2 ^ (4 * k + 2) * 2 ^ 1) % 10 = (2 ^ (4 * k + 2) % 10 * (2 ^ 1 % 10)) % 10 := by rw [Nat.mul_mod]
        _ = (4 * 2) % 10 := by rw [hcycle2 k]; norm_num
        _ = 8 := by norm_num
    -- Now prove the main result
    rcases hp4 with hp4 | hp4
    · -- p % 4 = 1: product ends in 6
      left
      -- p - 1 ≡ 0 mod 4
      have hp1_mod : (p - 1) % 4 = 0 := by omega
      -- Write p = 4 * (p / 4) + 1
      set k := p / 4 with hk_def
      have hp_eq : p = 4 * k + 1 := by omega
      have hp1_eq : p - 1 = 4 * k := by omega
      -- k ≥ 1 since p ≥ 5
      have hk_pos : k ≥ 1 := by omega
      -- 2^(4k) % 10 = 6
      have h1 : (2 ^ (4 * k)) % 10 = 6 := hcycle0 k hk_pos
      -- 2^(4k+1) % 10 = 2
      have h2 : (2 ^ (4 * k + 1)) % 10 = 2 := hcycle1 k
      -- (2^(4k+1) - 1) % 10 = 1
      have h3 : (2 ^ (4 * k + 1) - 1) % 10 = 1 := by
        have : 2 ^ (4 * k + 1) ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
        omega
      -- Product: (2^(4k) * (2^(4k+1) - 1)) % 10 = (6 * 1) % 10 = 6
      rw [hp1_eq, hp_eq]
      calc (2 ^ (4 * k) * (2 ^ (4 * k + 1) - 1)) % 10
          = ((2 ^ (4 * k)) % 10 * ((2 ^ (4 * k + 1) - 1) % 10)) % 10 := by rw [Nat.mul_mod]
        _ = (6 * 1) % 10 := by rw [h1, h3]
        _ = 6 := by norm_num
    · -- p % 4 = 3: product ends in 8
      right
      -- Write p = 4 * (p / 4) + 3
      set k := p / 4 with hk_def
      have hp_eq : p = 4 * k + 3 := by omega
      have hp1_eq : p - 1 = 4 * k + 2 := by omega
      have hk_pos : k ≥ 0 := by omega
      -- 2^(4k+2) % 10 = 4
      have h1 : (2 ^ (4 * k + 2)) % 10 = 4 := hcycle2 k
      -- 2^(4k+3) % 10 = 8
      have h2 : (2 ^ (4 * k + 3)) % 10 = 8 := hcycle3 k
      -- (2^(4k+3) - 1) % 10 = 7
      have h3 : (2 ^ (4 * k + 3) - 1) % 10 = 7 := by
        have : 2 ^ (4 * k + 3) ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
        omega
      -- Product: (2^(4k+2) * (2^(4k+3) - 1)) % 10 = (4 * 7) % 10 = 8
      rw [hp1_eq, hp_eq]
      calc (2 ^ (4 * k + 2) * (2 ^ (4 * k + 3) - 1)) % 10
          = ((2 ^ (4 * k + 2)) % 10 * ((2 ^ (4 * k + 3) - 1) % 10)) % 10 := by rw [Nat.mul_mod]
        _ = (4 * 7) % 10 := by rw [h1, h3]
        _ = 8 := by norm_num

/-- Every even perfect number ends in 6 or 8 (its last decimal digit is 6 or 8). -/
