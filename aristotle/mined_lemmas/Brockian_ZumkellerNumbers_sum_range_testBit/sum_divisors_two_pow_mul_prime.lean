import Mathlib

namespace Brockian.ZumkellerNumbers


lemma sum_divisors_two_pow_mul_prime (k p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    ∑ d ∈ (2 ^ k * p).divisors, d = (∑ i ∈ Finset.range (k + 1), 2 ^ i) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p := by
    refine Nat.Coprime.pow_left k ?_
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    rw [Nat.odd_iff] at hodd
    omega
  have hmul := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
  rw [ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply] at hmul
  rw [hmul]
  congr 1
  · exact Nat.sum_divisors_prime_pow Nat.prime_two
  · rw [hp.divisors, Finset.sum_pair hp.one_lt.ne]; omega

/-- If `p` is an odd prime with `p < 2 ^ (k + 1)`, then `2 ^ k * p` is a Zumkeller number:
its divisors split into two parts of equal sum.

The hypothesis `1 ≤ k` is part of the requested statement; the proof does not need it. -/
