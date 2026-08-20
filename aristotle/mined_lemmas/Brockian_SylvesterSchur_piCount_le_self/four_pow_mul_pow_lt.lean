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

theorem four_pow_mul_pow_lt {N k : ℕ} (hk : 4 ≤ k) (hkN : 2 * k ≤ N) :
    4 ^ k * N ^ k < k * ((2 * k) ^ k * N.choose k) := by
  have h1 : 4 ^ k < k * Nat.centralBinom k := Nat.four_pow_lt_mul_centralBinom k hk
  have h2 := centralBinom_mul_pow_le hkN
  calc 4 ^ k * N ^ k < (k * Nat.centralBinom k) * N ^ k :=
        mul_lt_mul_of_pos_right h1 (Nat.pow_pos (by omega))
    _ = k * (Nat.centralBinom k * N ^ k) := by ring
    _ ≤ k * ((2 * k) ^ k * N.choose k) := Nat.mul_le_mul_left _ h2

/-! ### The first case: `N` large compared to `k` -/

