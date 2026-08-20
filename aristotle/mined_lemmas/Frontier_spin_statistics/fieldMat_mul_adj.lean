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

theorem fieldMat_mul_adj (x y : Fin 4 → ℝ) :
    fieldMat x * (fieldMat y)ᴴ
      = !![dCoeff x * conj (dCoeff y), 0; 0, cCoeff x * conj (cCoeff y)] := by
  rw [fieldMat_conjTranspose, fieldMat, Matrix.mul_fin_two]
  norm_num

