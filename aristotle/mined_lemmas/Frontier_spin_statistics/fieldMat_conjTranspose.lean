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

theorem fieldMat_conjTranspose (x : Fin 4 → ℝ) :
    (fieldMat x)ᴴ = !![0, conj (cCoeff x); conj (dCoeff x), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fieldMat]

