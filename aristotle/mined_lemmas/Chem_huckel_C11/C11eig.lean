/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

noncomputable def C11eig (k : Fin 11) : ℝ := 2 * Real.cos (2 * Real.pi * k / 11)

/-- The (discrete Fourier / Vandermonde) matrix diagonalizing `C11adj`. -/
