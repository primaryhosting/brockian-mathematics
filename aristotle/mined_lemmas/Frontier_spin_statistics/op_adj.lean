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

theorem op_adj (M : Matrix (Fin 2) (Fin 2) ℂ) (x y : Hf) :
    ⟪op Mᴴ x, y⟫_ℂ = ⟪x, op M y⟫_ℂ := by
  have h : op Mᴴ = ContinuousLinearMap.adjoint (op M) := by
    rw [op, op, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    rfl
  rw [h, ContinuousLinearMap.adjoint_inner_left]

