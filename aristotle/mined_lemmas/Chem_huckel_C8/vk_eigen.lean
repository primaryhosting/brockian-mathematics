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

lemma vk_eigen (k : ℕ) (i : Fin 8) :
    vk k (i - 1) + vk k (i + 1) = (2 * Real.cos (theta k)) * vk k i := by
  have h1 : vk k (i + 1) = gk k ((i.val : ℤ) + 1) := gk_congr k (val_succ_mod i)
  have h2 : vk k (i - 1) = gk k ((i.val : ℤ) - 1) := gk_congr k (val_pred_mod i)
  rw [h1, h2]
  simp only [vk, gk]
  push_cast
  rw [show theta k * ((i.val : ℝ) - 1) = theta k * (i.val : ℝ) - theta k by ring,
      show theta k * ((i.val : ℝ) + 1) = theta k * (i.val : ℝ) + theta k by ring,
      Real.cos_sub, Real.cos_add]
  ring

