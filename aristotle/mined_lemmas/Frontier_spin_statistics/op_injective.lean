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

theorem op_injective {M : Matrix (Fin 2) (Fin 2) ℂ} (h : op M = 0) : M = 0 := by
  ext i j
  have hij := op_entry M i j
  rw [h] at hij
  simpa using hij.symm

/-- The vacuum vector. -/
