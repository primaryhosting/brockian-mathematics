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

lemma omega3_quad : omega3 ^ 2 + omega3 + 1 = 0 := by
  have h : (omega3 - 1) * (omega3 ^ 2 + omega3 + 1) = 0 := by linear_combination omega3_pow_three
  rcases mul_eq_zero.1 h with h1 | h1
  · exact absurd (by linear_combination h1 : omega3 = 1) omega3_ne_one
  · exact h1

