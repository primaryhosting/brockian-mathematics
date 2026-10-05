import Mathlib
/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

/-- Telescoping partial-sum estimate: for `N ≥ 1`,
`∑_{i < n} 1/(i+N)^2 ≤ 1/(N - 1/2) - 1/(N + n - 1/2)`.
Proved by induction on `n`, using `1/x^2 ≤ 1/(x - 1/2) - 1/(x + 1/2)`. -/

lemma tsum_inv_sq_shift_le (N : ℕ) (hN : 1 ≤ N) :
    ∑' i : ℕ, (((i : ℝ) + N) ^ 2)⁻¹ ≤ 2 / N := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  refine (summable_inv_sq_shift N).tsum_le_of_sum_range_le (fun n => ?_)
  refine (partial_sum_inv_sq_shift_le N hN n).trans ?_
  have hpos : (0 : ℝ) < (N : ℝ) + n - 1 / 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h1 : 1 / ((N : ℝ) - 1 / 2) ≤ 2 / N := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have h2 : 0 ≤ 1 / ((N : ℝ) + n - 1 / 2) := le_of_lt (by positivity)
  linarith

/-- **Singular series convergence rate.**

Let `a : ℕ → ℝ` be the local (arithmetic) terms of a singular series, i.e. we think of
`𝔖 = ∑' q, a q`, and assume the standard effective bound `|a q| ≤ C / q ^ 2` for every
modulus `q ≥ 1`. Then the singular series converges absolutely, and the truncation at
level `N` has error at most `2 * C / N`:

`|𝔖 - ∑_{q < N} a q| ≤ 2 * C / N`.

The rate is effective: the implied constant `2 * C` is explicit. -/
