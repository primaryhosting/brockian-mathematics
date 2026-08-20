/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The banner above is repeated as a module docstring below; Lean does not allow a
-- `/-! ... -/` module docstring to precede the `import` line.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ComplexConjugate

namespace QI

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

/-- A family of vectors `u k : A → ℂ` (`k : ι`) is orthonormal for the standard
Hermitian inner product on `ℂ^A`. -/

theorem mem_eigSp_iff {R : Matrix A A ℂ} {t : ℂ} {x : A → ℂ} :
    x ∈ eigSp R t ↔ ∀ i, ∑ i', R i i' * x i' = t * x i := by
  simp [eigSp, funext_iff, Matrix.mulVec, dotProduct]

omit [DecidableEq B] in
/-- Contraction of two expansions in an orthonormal family. -/
