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

lemma unitary_of_mul {U : Matrix n n ℂ} (h1 : U * Uᴴ = 1) (h2 : Uᴴ * U = 1) :
    U ∈ unitary (Matrix n n ℂ) := Unitary.mem_iff.mpr ⟨h2, h1⟩

/-- Inverse of a matrix presented as a unitary conjugate of an invertible diagonal matrix. -/
