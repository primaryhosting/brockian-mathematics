/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Topology

namespace Brockian

/-- The local factor deficiency `1/(p-1)^2` occurring in the twin-prime singular series. -/

lemma singularPartial_ge_half (N : ℕ) : 1 / 2 ≤ singularPartial N := by
  rcases le_or_gt 4 N with h | h
  · obtain ⟨-, -, hPge⟩ := tailProd_bounds (M := 4) (N := N) (by norm_num)
    rw [singularPartial_split (M := 4) (by norm_num) h, singularPartial_four]
    norm_num at hPge ⊢
    linarith
  · have := singularPartial_antitone (show N ≤ 3 by omega)
    rw [singularPartial_three] at this
    linarith

/-- **Singular series convergence rate.**  The truncated twin-prime singular series
`∏_{3 ≤ p ≤ N, p prime} (1 - 1/(p-1)^2)` converges to a limit `L ≥ 1/2`, and the
truncation at level `N ≥ 2` approximates `L` with the effective error bound `1/(N-1)`. -/
