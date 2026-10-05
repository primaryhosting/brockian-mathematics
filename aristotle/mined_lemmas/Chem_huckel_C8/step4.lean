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

lemma step4 {v : Fin 8 → ℝ} {μ : ℝ} (H : ∀ i, v (i - 1) + v (i + 1) = μ * v i) (i : Fin 8) :
    2 * v (i + 4) = ((μ ^ 2 - 2) ^ 2 - 2) * v i := by
  have a := step2 H (i - 2)
  rw [fin8_sub_two_sub_two, fin8_sub_two_add_two] at a
  have b := step2 H (i + 2)
  rw [fin8_add_two_sub_two, fin8_add_two_add_two] at b
  have c := step2 H i
  linear_combination a + b + (μ ^ 2 - 2) * c

/-- The characteristic relation satisfied by any eigenvalue. -/
