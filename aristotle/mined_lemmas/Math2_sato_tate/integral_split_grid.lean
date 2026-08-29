/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma integral_split_grid (t : ℕ → ℝ) (F : ℝ → ℝ) (hF : Continuous F) (n : ℕ) :
    (∑ j ∈ Finset.range n, ∫ x in (t j)..(t (j + 1)), F x) = ∫ x in (t 0)..(t n), F x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)

