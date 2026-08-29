import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

section Defs

variable {n m : Type*}

/-- The density matrix `|ψ⟩⟨ψ|` of a state vector `ψ` of a composite system whose
product basis is indexed by `n × m`. -/

theorem exists_unitary_mul_eq [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {A B : Matrix n m ℂ} (h : A * Aᴴ = B * Bᴴ) :
    ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧ B = A * U := by
  obtain ⟨W, hW⟩ := exists_linearIsometry_comp (Matrix.toEuclideanLin Aᴴ)
    (Matrix.toEuclideanLin Bᴴ) (norm_toEuclideanLin_conjTranspose_eq h)
  obtain ⟨V, hVmem, hV⟩ := exists_unitary_of_linearIsometry W
  refine ⟨Vᴴ, ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hVmem
  · have hmat : Matrix.toEuclideanLin (V * Aᴴ) = Matrix.toEuclideanLin Bᴴ := by
      apply LinearMap.ext
      intro x
      have h1 : Matrix.toEuclideanLin (V * Aᴴ) x
          = Matrix.toEuclideanLin V (Matrix.toEuclideanLin Aᴴ x) := by
        simp
      rw [h1, hV, hW x]
    have h2 : V * Aᴴ = Bᴴ := Matrix.toEuclideanLin.injective hmat
    have h3 := congrArg Matrix.conjTranspose h2
    simpa [Matrix.conjTranspose_mul] using h3.symm

/-- If `A Aᴴ = B Bᴴ` and the second index type of `A` embeds into that of `B`, then `B = A V`
for some isometry `V` (a matrix with orthonormal rows, `V Vᴴ = 1`). -/
