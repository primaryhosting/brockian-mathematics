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

lemma C3_charpoly : C3adj.charpoly = (X - C 2) * (X + C 1) ^ 2 := by
  rw [Matrix.charpoly, Matrix.det_fin_three, C_ofNat 2, map_one]
  simp [C3adj]
  ring

/-- A real number is an eigenvalue of the `C₃` adjacency matrix iff it is `2` or `-1`. -/
