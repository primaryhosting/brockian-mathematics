import RequestProject.Kron

/-!
# Vectorization, the modular operator and relative entropy

We vectorize matrices, express the relative entropy `Tr ρ log ρ - Tr ρ log σ` as (minus) a
quadratic form of `log (σ ⊗ (ρ⁻¹)ᵀ)` at the vectorization of `√ρ`, and record the
variational ("completing the square") characterization of resolvent quadratic forms.
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators MatrixOrder

namespace QI

variable {n m N : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype N] [DecidableEq N]

/-! ### Vectorization -/

/-- Vectorization of a matrix: the vector of all its entries, indexed by pairs. -/

lemma dot_herm_symm {S : Matrix N N ℂ} (hS : S.IsHermitian) (x y : N → ℂ) :
    star x ⬝ᵥ (S *ᵥ y) = starRingEnd ℂ (star y ⬝ᵥ (S *ᵥ x)) := by
  rw [dotProduct_mulVec, show star x ᵥ* S = star (S *ᵥ x) by rw [Matrix.star_mulVec, hS],
    star_dotProduct]
  simp

omit [DecidableEq N] in
