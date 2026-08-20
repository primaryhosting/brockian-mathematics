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

theorem log_eight_thirds_ge : (0.943 : ℝ) ≤ Real.log (8 / 3) := by
  have he : Real.log (8 / 3) = Real.log 2 + Real.log (4 / 3) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h43 : (1 : ℝ) - 1 / (4 / 3) ≤ Real.log (4 / 3) := one_sub_inv_le_log (by norm_num)
  rw [he]; norm_num at h43 ⊢; linarith [log_two_ge]

