import Mathlib
/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Chem

/-- The Hückel (adjacency) matrix of the cycle `C₄`: `A i j = 1` exactly when the carbon
atoms `i` and `j` are neighbours in the four-membered ring. -/

lemma huckel_cos_one : 2 * Real.cos (2 * Real.pi * (1 : ℕ) / 4) = 0 := by
  rw [show (2 * Real.pi * (1 : ℕ) / 4 : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, mul_zero]

