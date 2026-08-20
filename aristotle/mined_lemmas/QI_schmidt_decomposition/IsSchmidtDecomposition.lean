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

def IsSchmidtDecomposition {r : ℕ} (psi : A → B → ℂ) (s : Fin r → ℝ)
    (u : Fin r → A → ℂ) (v : Fin r → B → ℂ) : Prop :=
  (∀ k, 0 < s k) ∧ IsOrthonormalFamily u ∧ IsOrthonormalFamily v ∧
    ∀ i j, psi i j = ∑ k, (s k : ℂ) * u k i * v k j

/-- The (unnormalised) reduced density matrix of the first factor. -/
