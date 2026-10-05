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

lemma singularPartial_cauchy {M N : ℕ} (h2 : 2 ≤ M) (hMN : M ≤ N) :
    |singularPartial N - singularPartial M| ≤ 1 / ((M : ℝ) - 1) := by
  obtain ⟨hP0, hP1, hPge⟩ := tailProd_bounds (M := M) (N := N) h2
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h2
  have hSM0 := singularPartial_nonneg M
  have hSM1 := singularPartial_le_one M
  have hbnd0 : 0 ≤ 1 / ((M : ℝ) - 1) := by
    have : (0 : ℝ) < (M : ℝ) - 1 := by linarith
    positivity
  rw [singularPartial_split h2 hMN, abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- The truncation at level `3` equals `1 - 1/4 = 3/4`. -/
