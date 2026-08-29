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

lemma abel_sum_aux (g M : ℕ → ℝ) (n : ℕ) (hM0 : M 0 = 0) :
    (∑ j ∈ Finset.range n, (g j - g (j + 1)) * M j) + g n * M n
      = ∑ j ∈ Finset.range n, g (j + 1) * (M (j + 1) - M j) := by
  induction n with
  | zero => simp [hM0]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith [ih]

