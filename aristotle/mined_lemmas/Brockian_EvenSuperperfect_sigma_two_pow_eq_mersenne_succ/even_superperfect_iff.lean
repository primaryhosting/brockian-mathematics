import Mathlib
namespace Brockian.EvenSuperperfect

namespace EuclidEuler
namespace Nat

open ArithmeticFunction Finset
open scoped sigma


theorem even_superperfect_iff (n : ℕ) (hn : 0 < n) (he : Even n) :
    ArithmeticFunction.sigma 1 (ArithmeticFunction.sigma 1 n) = 2 * n ↔
      ∃ p : ℕ, (2 ^ p - 1).Prime ∧ n = 2 ^ (p - 1) := by
  constructor
  · -- Forward: σ(σ(n)) = 2n → n = 2^(p-1) with 2^p - 1 prime
    intro hσ
    obtain ⟨k, rfl⟩ := eq_two_pow_of_even_superperfect n hn he hσ
    use k + 1
    constructor
    · -- Show 2^(k+1) - 1 is prime
      -- We have σ(σ(2^k)) = 2 * 2^k = 2^(k+1)
      -- And σ(2^k) = 2^(k+1) - 1
      -- So σ(2^(k+1) - 1) = 2^(k+1) = (2^(k+1) - 1) + 1
      -- For m > 1, σ(m) = m + 1 iff m is prime
      have hσ2k : (sigma 1) (2 ^ k) = 2 ^ (k + 1) - 1 := by
        rw [EuclidEuler.Nat.sigma_two_pow_eq_mersenne_succ, mersenne]
      have hSS_eq : (sigma 1) (2 ^ (k + 1) - 1) = 2 ^ (k + 1) := by
        rw [← hσ2k]
        convert hσ using 1
        ring
      -- sum_properDivisors = σ(m) - m = 1, so m is prime
      have hk_pos : k ≥ 1 := by
        by_contra hk0
        push_neg at hk0
        interval_cases k
        simp [even_iff_two_dvd] at he
      have hm_gt_1 : 2 ^ (k + 1) - 1 > 1 := by
        have h1 : 2 ^ (k + 1) > 2 := by
          have : 1 < k + 1 := Nat.lt_succ_of_le hk_pos
          exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) this
        omega
      have hsum_prop : ∑ i ∈ Nat.properDivisors (2 ^ (k + 1) - 1), i = 1 := by
        simp only [sigma_one_apply] at hSS_eq
        rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at hSS_eq
        omega
      exact Nat.sum_properDivisors_eq_one_iff_prime.mp hsum_prop
    · simp
  · -- Backward: n = 2^(p-1) with 2^p - 1 prime → σ(σ(n)) = 2n
    rintro ⟨p, hp_prime, rfl⟩
    -- n = 2^(p-1), need to show σ(σ(n)) = 2n
    -- σ(n) = σ(2^(p-1)) = mersenne(p) = 2^p - 1
    -- Since 2^p - 1 is prime, σ(2^p - 1) = 1 + (2^p - 1) = 2^p = 2 * 2^(p-1) = 2n
    have hp_pos : 0 < p := by
      by_contra hp0
      push_neg at hp0
      interval_cases p
      exact Nat.not_prime_zero hp_prime
    have hσ1 : (sigma 1) (2 ^ (p - 1)) = 2 ^ p - 1 := by
      rw [EuclidEuler.Nat.sigma_two_pow_eq_mersenne_succ, mersenne, Nat.sub_add_cancel hp_pos]
    rcases p with ⟨⟩
    · contradiction
    · -- p = n + 1
      rename_i n
      rw [hσ1]
      -- Now need σ(2^(n+1) - 1) = 2 * 2^n
      -- Since 2^(n+1) - 1 is prime, σ(2^(n+1) - 1) = 1 + (2^(n+1) - 1) = 2^(n+1)
      have hprime : Nat.Prime (2 ^ (n + 1) - 1) := hp_prime
      rw [sigma_one_apply]
      -- For prime p, divisors are {1, p}, sum is 1 + p
      rw [Nat.Prime.sum_divisors hprime]
      simp [pow_succ]
      rw [Nat.sub_add_cancel (by linarith [pow_pos (by norm_num : 0 < (2:ℕ)) n] : 1 ≤ 2 ^ n * 2)]
      ring
end Brockian.EvenSuperperfect

