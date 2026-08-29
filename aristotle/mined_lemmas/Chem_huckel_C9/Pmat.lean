import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

noncomputable def Pmat : Matrix (ZMod 9) (ZMod 9) ℂ := Matrix.of fun i k => ee (i * k)

/-- The conjugate Fourier matrix. -/
