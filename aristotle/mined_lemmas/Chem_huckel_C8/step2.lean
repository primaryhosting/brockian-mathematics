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

lemma step2 {v : Fin 8 → ℝ} {μ : ℝ} (H : ∀ i, v (i - 1) + v (i + 1) = μ * v i) (i : Fin 8) :
    v (i - 2) + v (i + 2) = (μ ^ 2 - 2) * v i := by
  have a := H (i - 1)
  rw [fin8_sub_one_sub_one, fin8_sub_one_add_one] at a
  have b := H (i + 1)
  rw [fin8_add_one_sub_one, fin8_add_one_add_one] at b
  have c := H i
  linear_combination a + b + μ * c

/-- Four steps of the recurrence. -/
