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

lemma quad_expand (S : Matrix N N ℂ) (x y : N → ℂ) :
    star (x - y) ⬝ᵥ (S *ᵥ (x - y))
      = star x ⬝ᵥ (S *ᵥ x) - star x ⬝ᵥ (S *ᵥ y) - star y ⬝ᵥ (S *ᵥ x)
        + star y ⬝ᵥ (S *ᵥ y) := by
  simp only [Matrix.mulVec_sub, star_sub, dotProduct_sub, sub_dotProduct]
  ring

/-- **Completing the square**: the resolvent quadratic form dominates the associated
"linear minus quadratic" functional. -/
