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

theorem IsOrthonormalFamily.conj_right {ι : Type*} [DecidableEq ι] {v : ι → B → ℂ}
    (h : IsOrthonormalFamily v) (k l : ι) :
    ∑ b, v k b * conj (v l b) = if k = l then 1 else 0 := by
  have := h l k
  rw [show (if l = k then (1 : ℂ) else 0) = (if k = l then (1 : ℂ) else 0) by
    simp [eq_comm]] at this
  rw [← this]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/-! ### Existence -/

/-- The spectral data of the Gram matrix `psiᴴ psi`: an orthonormal, complete family of
eigenvectors `w` with real eigenvalues `μ`. -/
