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

lemma singularTerm_le_one {p : ℕ} (hp : 3 ≤ p) : singularTerm p ≤ 1 := by
  have h : (2 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  unfold singularTerm
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- Weierstrass-type product inequality: `1 - ∑ f ≤ ∏ (1 - f)` for `f` valued in `[0,1]`. -/
