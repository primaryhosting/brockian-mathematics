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

lemma partial_sum_inv_sq_shift_le (N : ℕ) (hN : 1 ≤ N) (n : ℕ) :
    ∑ i ∈ Finset.range n, (((i : ℝ) + N) ^ 2)⁻¹
      ≤ 1 / ((N : ℝ) - 1 / 2) - 1 / ((N : ℝ) + n - 1 / 2) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    set x : ℝ := (N : ℝ) + n with hx
    have hx1 : (1 : ℝ) ≤ x := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      simp only [hx]; linarith
    have hpos1 : (0 : ℝ) < x - 1 / 2 := by linarith
    have hpos2 : (0 : ℝ) < x + 1 / 2 := by linarith
    have hpos3 : (0 : ℝ) < x ^ 2 - 1 / 4 := by nlinarith
    have key : (x ^ 2)⁻¹ ≤ 1 / (x - 1 / 2) - 1 / (x + 1 / 2) := by
      have heq : 1 / (x - 1 / 2) - 1 / (x + 1 / 2) = 1 / (x ^ 2 - 1 / 4) := by
        rw [div_sub_div _ _ (ne_of_gt hpos1) (ne_of_gt hpos2), div_eq_div_iff
          (by positivity) (ne_of_gt hpos3)]
        ring
      rw [heq, inv_eq_one_div]
      apply one_div_le_one_div_of_le
      · nlinarith
      · nlinarith
    have hcast : ((N : ℝ) + (↑(n + 1) : ℝ) - 1 / 2) = x + 1 / 2 := by
      push_cast; simp only [hx]; ring
    rw [hcast]
    have hxn : ((n : ℝ) + (N : ℝ)) = x := by simp only [hx]; ring
    rw [hxn]
    linarith

/-- The shifted inverse-square series is summable. -/
