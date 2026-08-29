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

lemma C3_cos_one : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  rw [show (2 * Real.pi / 3) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]

/-- `2 cos (2π·2/3) = -1`. -/
