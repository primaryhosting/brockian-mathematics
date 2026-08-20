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

theorem one_sub_inv_le_log {z : ℝ} (hz : 0 < z) : 1 - 1 / z ≤ Real.log z := by
  have h := Real.log_le_sub_one_of_pos (x := 1 / z) (by positivity)
  rw [Real.log_div one_ne_zero hz.ne', Real.log_one] at h
  linarith

/-- A convenient upper bound: `log (v ^ 4) ≤ 7.1 + v / 4`. -/
