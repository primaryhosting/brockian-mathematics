import Mathlib
namespace Brockian.SylvesterSchur

/-!
# The Sylvester–Schur theorem

If `n > k ≥ 1` then one of `n+1, …, n+k` has a prime factor `> k`.

The proof follows Erdős' argument: assuming the contrary, every prime factor of the
binomial coefficient `(n+k).choose k` is at most `k`.  This yields two upper bounds for
that binomial coefficient (one via the number of primes `≤ k`, one via the primorial),
both of which are contradicted by an elementary lower bound, except in a range of small
parameters which is covered by an explicit chain of primes.
-/

open Finset Real

/-! ### An elementary upper bound for the prime counting function -/

/-- The number of primes `≤ k`. -/

theorem pow_eleven_lt_four_pow {k : ℕ} (hk : 26 ≤ k) : k ^ 11 < 4 ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 26 with h | h
    · have he : n + 1 = 26 := by omega
      rw [he]; norm_num
    · have ihn := ih (by omega)
      have step : (n + 1) ^ 11 ≤ 4 * n ^ 11 := by
        have h1 : 26 * (n + 1) ≤ 27 * n := by omega
        have h2 : (26 * (n + 1)) ^ 11 ≤ (27 * n) ^ 11 := Nat.pow_le_pow_left h1 11
        rw [mul_pow, mul_pow] at h2
        have h3 : (27 : ℕ) ^ 11 * n ^ 11 ≤ (4 * 26 ^ 11) * n ^ 11 :=
          Nat.mul_le_mul_right _ (by norm_num)
        have h4 : (26 : ℕ) ^ 11 * (n + 1) ^ 11 ≤ 26 ^ 11 * (4 * n ^ 11) := by
          calc (26 : ℕ) ^ 11 * (n + 1) ^ 11 ≤ 27 ^ 11 * n ^ 11 := h2
            _ ≤ (4 * 26 ^ 11) * n ^ 11 := h3
            _ = 26 ^ 11 * (4 * n ^ 11) := by ring
        exact Nat.le_of_mul_le_mul_left h4 (by positivity)
      calc (n + 1) ^ 11 ≤ 4 * n ^ 11 := step
        _ < 4 * 4 ^ n := by omega
        _ = 4 ^ (n + 1) := by ring

