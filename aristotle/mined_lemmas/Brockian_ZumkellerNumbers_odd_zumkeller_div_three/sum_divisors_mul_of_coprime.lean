import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

lemma sum_divisors_mul_of_coprime {m k : ℕ} (h : m.Coprime k) :
    ∑ d ∈ (m * k).divisors, d = (∑ d ∈ m.divisors, d) * (∑ d ∈ k.divisors, d) := by
  simpa [ArithmeticFunction.sigma_one_apply] using
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime h

/-- `σ(5391411025) = 10799308800`, computed from the factorization
`5391411025 = 5^2 * 7 * 11 * 13 * 17 * 19 * 23 * 29`. -/
