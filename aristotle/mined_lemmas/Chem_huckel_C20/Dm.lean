import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Matrix Polynomial Finset

/-- A primitive 20-th root of unity. -/

noncomputable def Dm : Matrix (Fin 20) (Fin 20) ℂ :=
  Matrix.diagonal (fun k => ee k + (ee k)⁻¹)

