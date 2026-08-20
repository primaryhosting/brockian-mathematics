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

theorem caseA {N k q : ℕ} (hk : 26 ≤ k) (h : k ^ 3 ≤ N ^ 2) (hq : 3 * q ≤ k + 9) :
    k ^ (k + 1) < 2 ^ k * N ^ (k - q) := by
  set d := k - q with hddef
  have hd : 2 * k ≤ 3 * d + 9 := by omega
  have hk1 : 1 ≤ k := by omega
  obtain ⟨j, hj⟩ : ∃ j, 2 * k = j + 9 := ⟨2 * k - 9, by omega⟩
  have h1 : (k ^ 3) ^ d ≤ (N ^ 2) ^ d := Nat.pow_le_pow_left h d
  have h2 : k ^ j ≤ k ^ (3 * d) := Nat.pow_le_pow_right hk1 (by omega)
  have h3 : k ^ 11 < 4 ^ k := pow_eleven_lt_four_pow hk
  have hkey : (k ^ (k + 1)) ^ 2 < (2 ^ k * N ^ d) ^ 2 := by
    have e1 : (k ^ (k + 1)) ^ 2 = k ^ 11 * k ^ j := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    have e2 : (2 ^ k * N ^ d) ^ 2 = 4 ^ k * (N ^ 2) ^ d := by
      rw [mul_pow, ← pow_mul, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      ring_nf
    rw [e1, e2]
    calc k ^ 11 * k ^ j < 4 ^ k * k ^ j :=
          mul_lt_mul_of_pos_right h3 (Nat.pow_pos (by omega))
      _ ≤ 4 ^ k * (N ^ 2) ^ d := by
          have hle : k ^ j ≤ (N ^ 2) ^ d := by
            calc k ^ j ≤ k ^ (3 * d) := h2
              _ = (k ^ 3) ^ d := by rw [← pow_mul]
              _ ≤ (N ^ 2) ^ d := h1
          exact Nat.mul_le_mul_left _ hle
  exact lt_of_pow_lt_pow_left' 2 hkey

/-! ### The second case: `N` comparable to `k` -/

/-! ### Elementary bounds on the logarithm -/

