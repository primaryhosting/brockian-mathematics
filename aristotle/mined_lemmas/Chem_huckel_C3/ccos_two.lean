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

lemma ccos_two : Complex.cos (2 * (Real.pi : ℂ) * 2 / 3) = -(1 / 2) := by
  have h : ((Real.cos (2 * Real.pi * 2 / 3) : ℝ) : ℂ)
      = Complex.cos ((2 * Real.pi * 2 / 3 : ℝ) : ℂ) := Complex.ofReal_cos _
  rw [show (2 * (Real.pi : ℂ) * 2 / 3) = ((2 * Real.pi * 2 / 3 : ℝ) : ℂ) by push_cast; ring, ← h,
    show (2 * Real.pi * 2 / 3) = Real.pi + Real.pi / 3 by ring, Real.cos_add,
    Real.cos_pi_div_three, Real.sin_pi, Real.cos_pi]
  push_cast; ring

/-- **Explicit Hückel eigenvectors of `C₃`.** For each `k ∈ {0, 1, 2}` the Bloch vector
`c3vec k` is a nonzero eigenvector of the `C₃` adjacency matrix with eigenvalue
`2 * cos (2πk/3)`. -/
