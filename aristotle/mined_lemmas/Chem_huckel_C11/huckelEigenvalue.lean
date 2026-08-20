import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial Finset

namespace Chem

/-- A primitive 11th root of unity. -/

noncomputable def huckelEigenvalue (k : Fin 11) : ℂ :=
  2 * ((Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℝ) : ℂ)

/-- The discrete Fourier transform matrix, whose columns are the eigenvectors. -/
