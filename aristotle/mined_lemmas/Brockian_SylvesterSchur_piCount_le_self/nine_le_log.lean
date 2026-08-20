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

theorem nine_le_log {x : ℝ} (hx : 20000 ≤ x) : 9 ≤ Real.log x := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h : Real.exp 9 ≤ 20000 := by
    have he : Real.exp 9 = (Real.exp 1) ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    have h2 : (Real.exp 1) ^ 9 ≤ (2.7182818286 : ℝ) ^ 9 := by gcongr
    linarith [h2, show (2.7182818286 : ℝ) ^ 9 ≤ 20000 by norm_num]
  have h3 := Real.log_le_log (Real.exp_pos 9) (le_trans h hx)
  rwa [Real.log_exp] at h3

