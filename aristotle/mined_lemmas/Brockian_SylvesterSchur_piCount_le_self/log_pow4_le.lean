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

theorem log_pow4_le {v : ℝ} (hv : 0 < v) : Real.log (v ^ 4) ≤ 7.1 + v / 4 := by
  have h16 : Real.log (v / 16) ≤ v / 16 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hl : Real.log v = Real.log (v / 16) + Real.log 16 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]; ring_nf
  have h2 : Real.log 16 ≤ 2.7725888 := by
    have h16' : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  rw [Real.log_pow]
  push_cast
  linarith

