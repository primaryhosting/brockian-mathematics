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

lemma eigen_poly {v : Fin 8 → ℝ} {μ : ℝ} (hv : v ≠ 0)
    (H : ∀ i, v (i - 1) + v (i + 1) = μ * v i) :
    (((μ ^ 2 - 2) ^ 2 - 2) ^ 2 - 4) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext fun i => h i)
  have a := step4 H i
  have b := step4 H (i + 4)
  rw [fin8_add_four_add_four] at b
  have key : ((((μ ^ 2 - 2) ^ 2 - 2) ^ 2 - 4)) * v i = 0 := by
    linear_combination (-((μ ^ 2 - 2) ^ 2 - 2)) * a - 2 * b
  exact (mul_eq_zero.mp key).resolve_right hi

