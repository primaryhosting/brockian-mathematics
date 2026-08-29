import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

lemma sum_divisors_5391411025 : ∑ d ∈ (5391411025 : ℕ).divisors, d = 10799308800 := by
  have h : (5391411025 : ℕ) = 25 * 7 * 11 * 13 * 17 * 19 * 23 * 29 := by norm_num
  rw [h, sum_divisors_mul_of_coprime (by norm_num), sum_divisors_mul_of_coprime (by norm_num),
    sum_divisors_mul_of_coprime (by norm_num), sum_divisors_mul_of_coprime (by norm_num),
    sum_divisors_mul_of_coprime (by norm_num), sum_divisors_mul_of_coprime (by norm_num),
    sum_divisors_mul_of_coprime (by norm_num)]
  decide

/-- The six divisors `1, 23, 391, 135575, 8107385, 5391411025` of `5391411025` sum to exactly
half of `σ(5391411025)`; hence `5391411025` is a Zumkeller number. -/
