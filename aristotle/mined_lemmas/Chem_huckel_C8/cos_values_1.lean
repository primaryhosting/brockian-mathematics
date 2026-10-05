/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real Matrix SimpleGraph

namespace Chem

/-- The adjacency matrix (over `ℝ`) of the cycle graph `C₈`, i.e. the Hückel matrix of
cyclooctatetraene in units where `α = 0` and `β = 1`. -/

lemma cos_values_1 : 2 * Real.cos (2 * π * (1 : ℕ) / 8) = Real.sqrt 2 := by
  rw [show 2 * π * ((1 : ℕ) : ℝ) / 8 = π / 4 by push_cast; ring, Real.cos_pi_div_four]
  ring

