/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of a
16-membered annulene, with `α = 0`, `β = 1`). -/

theorem C16_charpoly :
    C16.charpoly = ∏ k : Fin 16, (X - C (huckelLevel k)) := by
  rw [C16_eq_conj]
  have := Matrix.charpoly_units_conj dft16_isUnit.unit (Matrix.diagonal huckelLevel)
  rw [Matrix.coe_units_inv, IsUnit.unit_spec] at this
  rw [this, Matrix.charpoly_diagonal]

