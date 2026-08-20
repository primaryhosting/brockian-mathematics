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

lemma krausMap_ampliation_posSemidef {p : Type*} [Fintype p] [DecidableEq p]
    (K : ι → Matrix m n ℂ) {X : Matrix (p × n) (p × n) ℂ} (hX : X.PosSemidef) :
    (∑ i, ((1 : Matrix p p ℂ) ⊗ₖ K i) * X * ((1 : Matrix p p ℂ) ⊗ₖ K i)ᴴ).PosSemidef := by
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    (Matrix.PosSemidef.zero) (fun i _ => ?_)
  have := hX.conjTranspose_mul_mul_same (((1 : Matrix p p ℂ) ⊗ₖ K i)ᴴ)
  rwa [Matrix.conjTranspose_conjTranspose] at this

/-! ### The stacked isometry and the Kadison–Schwarz inequality -/

/-- The Kraus operators stacked into a single tall matrix. -/
