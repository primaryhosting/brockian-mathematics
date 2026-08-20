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

noncomputable def dftMatrix : Matrix (Fin 11) (Fin 11) ℂ := fun j k => ee (j * k)

/-- The (scaled) inverse discrete Fourier transform matrix. -/
