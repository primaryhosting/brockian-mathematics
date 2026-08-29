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

def C3adj : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if i = j then 0 else 1

/-- `2 cos (2π·0/3) = 2`. -/
