/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- The adjacency matrix of the cycle graph `C₃` (every pair of distinct vertices
is adjacent). In Hückel theory this is the (shifted, scaled) Hamiltonian of the
cyclic three-carbon π-system. -/

lemma ccos_one : Complex.cos (2 * (Real.pi : ℂ) / 3) = -(1 / 2) := by
  have h : ((Real.cos (2 * Real.pi / 3) : ℝ) : ℂ) = Complex.cos ((2 * Real.pi / 3 : ℝ) : ℂ) :=
    Complex.ofReal_cos _
  rw [show (2 * (Real.pi : ℂ) / 3) = ((2 * Real.pi / 3 : ℝ) : ℂ) by push_cast; ring, ← h,
    show (2 * Real.pi / 3) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]
  push_cast; ring

