import Mathlib

namespace Brockian.ZumkellerNumbers


lemma sum_range_two_pow_succ (k : ℕ) : (∑ i ∈ Finset.range (k + 1), 2 ^ i) + 1 = 2 ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ]; ring_nf; ring_nf at ih; omega

/-- The sum of the divisors of `2 ^ k * p` for an odd prime `p`. -/
