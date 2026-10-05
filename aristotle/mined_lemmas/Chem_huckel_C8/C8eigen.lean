import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial

namespace Chem

/-- A primitive 8-th root of unity. -/

noncomputable def C8eigen (k : Fin 8) : ℂ := 2 * Real.cos (2 * Real.pi * k / 8)

/-- The discrete Fourier transform matrix, whose columns are the eigenvectors of `C8adj`. -/
