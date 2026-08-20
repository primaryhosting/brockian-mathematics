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

theorem op_entry (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ⟪(EuclideanSpace.single i (1 : ℂ)), (op M) (EuclideanSpace.single j (1 : ℂ))⟫_ℂ = M i j := by
  rw [EuclideanSpace.inner_single_left]
  simp [op, Matrix.mulVec, dotProduct]

