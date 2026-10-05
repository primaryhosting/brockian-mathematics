import Mathlib

def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

lemma sigma1_two_pow (k : ℕ) : sigma1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  unfold sigma1
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      rw [pow_succ 2 (n + 1)]
      omega

/-- If `σ(m) = m + 1` then `m` is prime. -/
