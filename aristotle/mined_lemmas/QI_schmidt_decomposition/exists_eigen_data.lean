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

theorem exists_eigen_data (psi : A → B → ℂ) :
    ∃ (w : B → B → ℂ) (mu : B → ℝ),
      (∀ k l, ∑ b, conj (w k b) * w l b = if k = l then 1 else 0) ∧
      (∀ a b, ∑ j, w j a * conj (w j b) = if a = b then 1 else 0) ∧
      (∀ j a, ∑ b, (∑ i, conj (psi i a) * psi i b) * w j b = (mu j : ℂ) * w j a) := by
  set G : Matrix B B ℂ := Matrix.of (fun a b => ∑ i, conj (psi i a) * psi i b) with hG
  have hherm : G.IsHermitian := by
    ext a b
    simp only [Matrix.conjTranspose_apply, hG, Matrix.of_apply, star_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  refine ⟨fun j => (hherm.eigenvectorBasis j).ofLp, hherm.eigenvalues, ?_, ?_, ?_⟩
  · intro k l
    have hmem := hherm.eigenvectorUnitary.2
    rw [Unitary.mem_iff] at hmem
    have := congrFun (congrFun hmem.1 k) l
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using this
  · intro a b
    have hmem := hherm.eigenvectorUnitary.2
    rw [Unitary.mem_iff] at hmem
    have := congrFun (congrFun hmem.2 a) b
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using this
  · intro j a
    have := congrFun (hherm.mulVec_eigenvectorBasis j) a
    simpa [Matrix.mulVec, dotProduct, hG, Complex.real_smul] using this

