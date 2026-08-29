import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Real
open scoped ComplexOrder

namespace QI

/-! ## Von Neumann entropy and reduced density matrices -/

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a matrix, computed as the sum of
`negMulLog` over the eigenvalues.  (Defined to be `0` on non-Hermitian matrices.) -/

theorem isHermitian_diagonal_ofReal {n : Type*} [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal fun i => (d i : ℂ)).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [Matrix.diagonal_conjTranspose]

/-- The eigenvalue multiset of a real diagonal matrix is its diagonal, hence its von Neumann
entropy is the Shannon entropy of the diagonal. -/
