/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open scoped InnerProductSpace

namespace Frontier

/-! ## Minkowski geometry -/

/-- The Minkowski bilinear form on `ℝ⁴` with signature `(+,-,-,-)`. -/

theorem adj_mul_fieldMat (x y : Fin 4 → ℝ) :
    (fieldMat y)ᴴ * fieldMat x
      = !![conj (cCoeff y) * cCoeff x, 0; 0, conj (dCoeff y) * dCoeff x] := by
  rw [fieldMat_conjTranspose, fieldMat, Matrix.mul_fin_two]
  norm_num

/-- At spacelike separation the matrices of the model anticommute. -/
