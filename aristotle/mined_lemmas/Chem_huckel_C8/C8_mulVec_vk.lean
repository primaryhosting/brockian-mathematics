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

lemma C8_mulVec_vk (k : ℕ) : C8 *ᵥ vk k = (2 * Real.cos (theta k)) • vk k := by
  funext i
  rw [C8_mulVec, Pi.smul_apply, smul_eq_mul]
  exact vk_eigen k i

/-- Every `2 cos (2πk/8)` is an eigenvalue of the adjacency matrix of `C₈`. -/
