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

theorem sum_mul_sum_expand {I J : Type*} [Fintype I] [Fintype J] (F : I → ℂ) (G : J → ℂ) :
    (∑ a, F a) * (∑ b, G b) = ∑ a, ∑ b, F a * G b := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _

