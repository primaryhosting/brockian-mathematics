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

lemma huckel_C8_exists (k : ℕ) :
    ∃ v : Fin 8 → ℝ, v ≠ 0 ∧ C8 *ᵥ v = (2 * Real.cos (2 * π * k / 8)) • v :=
  ⟨vk k, vk_ne_zero k, C8_mulVec_vk k⟩

-- Index arithmetic in `Fin 8`.
