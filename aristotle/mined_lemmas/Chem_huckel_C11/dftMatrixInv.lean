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

noncomputable def dftMatrixInv : Matrix (Fin 11) (Fin 11) ℂ :=
  fun j k => (11 : ℂ)⁻¹ * ee (-(j * k))

