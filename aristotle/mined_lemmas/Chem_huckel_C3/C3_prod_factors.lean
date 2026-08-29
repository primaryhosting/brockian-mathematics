import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl,
in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/

lemma C3_prod_factors :
    ∏ k : Fin 3, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 3))) =
      (X - C 2) * (X + C 1) ^ 2 := by
  rw [Fin.prod_univ_three]
  norm_num [C3_cos_zero, C3_cos_one, C3_cos_two]
  ring

/-- The characteristic polynomial of the `C₃` adjacency matrix. -/
