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

lemma omega3_pow_three : omega3 ^ 3 = 1 := by
  rw [omega3, ← Complex.exp_nat_mul, show ((3 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 3)
    = 2 * Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_two_pi_mul_I

