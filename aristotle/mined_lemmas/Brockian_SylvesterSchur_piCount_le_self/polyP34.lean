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

theorem polyP34 {v w : ℝ} (hv : 11.8 ≤ v) (hw2 : w ^ 2 ≤ v ^ 6) :
    (7.1 + v / 4) + w * (10.65 + 0.375 * v) ≤ 1.45 * v ^ 4 := by
  have hv0 : (0 : ℝ) < v := by linarith
  have hvs : (0 : ℝ) ≤ v - 11.8 := by linarith
  have hw : w ≤ v ^ 3 := by
    by_contra hc
    rw [not_le] at hc
    have h3 : (0 : ℝ) < v ^ 3 := by positivity
    nlinarith [hc, h3]
  have e1 : 0 ≤ (v - 11.8) * v ^ 3 := mul_nonneg hvs (by positivity)
  have e2 : 0 ≤ (v - 11.8) * v ^ 2 := mul_nonneg hvs (by positivity)
  have e3 : 0 ≤ (v - 11.8) * v := mul_nonneg hvs (by positivity)
  nlinarith [e1, e2, e3, hw, hv0, sq_nonneg v]

/-! ### The analytic heart of the second case -/

set_option maxHeartbeats 1000000 in
