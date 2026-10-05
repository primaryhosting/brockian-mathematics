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

lemma C3_cos_two : Real.cos (2 * Real.pi * (2 : ℝ) / 3) = -(1 / 2) := by
  rw [show (2 * Real.pi * (2 : ℝ) / 3) = Real.pi + Real.pi / 3 by ring, Real.cos_add,
    Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
  ring

/-- The product of the linear factors `X - 2 cos (2πk/3)` is `(X - 2)(X + 1)²`. -/
