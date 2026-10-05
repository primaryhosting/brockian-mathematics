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

lemma omega3_exp_four : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (2 * 2) / 3) = omega3 := by
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (2 * 2) / 3)
      = ((4 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 3) by push_cast; ring,
    Complex.exp_nat_mul, ← omega3]
  calc omega3 ^ 4 = omega3 ^ 3 * omega3 := by ring
    _ = omega3 := by rw [omega3_pow_three, one_mul]

/-- The adjacency matrix of `C₃`, viewed over `ℂ`. -/
