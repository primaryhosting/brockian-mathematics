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

noncomputable def dCoeff (x : Fin 4 → ℝ) : ℂ :=
  if x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 then 1
  else if x 1 = 1 ∧ x 2 = 0 ∧ x 3 = 0 then -1 else 0

/-- The matrix of the field at a spacetime point. -/
