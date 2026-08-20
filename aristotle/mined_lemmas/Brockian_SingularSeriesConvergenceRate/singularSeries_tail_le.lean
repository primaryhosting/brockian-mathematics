/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header
-- above is written as an ordinary block comment and repeated as a module docstring below.)

import Mathlib

/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- The `p`-th term of the (twin-prime) singular series: `1/(p-1)^2` for odd primes `p`,
and `0` otherwise. -/

theorem singularSeries_tail_le {N : ℕ} (hN : 3 ≤ N) :
    ∑' i : ℕ, singularTerm (i + N) ≤ 1 / ((N : ℝ) - 2) := by
  refine Real.tsum_le_of_sum_le (fun i => singularTerm_nonneg _) (fun u => ?_)
  obtain ⟨m, hm⟩ : ∃ m, u ⊆ Finset.range m := ⟨(u.sup id) + 1, by
    intro x hx
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)⟩
  have h1 : ∑ i ∈ u, singularTerm (i + N) ≤ ∑ i ∈ Finset.range m, singularTerm (i + N) :=
    Finset.sum_le_sum_of_subset_of_nonneg hm (fun i _ _ => singularTerm_nonneg _)
  have h2 := sum_range_shift_singularTerm_le hN m
  have hpos : (0 : ℝ) ≤ 1 / ((m : ℝ) + (N : ℝ) - 2) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h4 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    exact div_nonneg (by norm_num) (by linarith)
  linarith

/-- Weierstrass product inequality: `1 - ∑ a ≤ ∏ (1 - a)` for `0 ≤ a i ≤ 1`. -/
