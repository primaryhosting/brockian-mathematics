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

lemma C3_cos_zero : Real.cos (2 * Real.pi * (0 : ℝ) / 3) = 1 := by norm_num

/-- `2 cos (2π·1/3) = -1`. -/
