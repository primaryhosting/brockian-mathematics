import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Matrix

namespace Chem

/-- A primitive 19-th root of unity. -/

noncomputable def G19 : Matrix (Fin 19) (Fin 19) ℂ :=
  Matrix.of fun j k => (19 : ℂ)⁻¹ * (omega19⁻¹) ^ (j.val * k.val)

/-- The `k`-th Hückel eigenvalue of the cycle `C₁₉`. -/
