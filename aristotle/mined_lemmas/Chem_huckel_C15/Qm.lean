import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

noncomputable def Qm : Matrix (Fin 15) (Fin 15) ℂ :=
  Matrix.of fun j l => (15 : ℂ)⁻¹ * ((g l) ^ (j.val))⁻¹

/-- The diagonal matrix of eigenvalues. -/
