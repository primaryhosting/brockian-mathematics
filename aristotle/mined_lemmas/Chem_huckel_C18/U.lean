import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Real Matrix Finset

/-- A primitive 18-th root of unity. -/

noncomputable def U : Matrix (ZMod 18) (ZMod 18) ℂ := Matrix.of fun j k => ee (j * k)

/-- The inverse of the discrete Fourier matrix. -/
