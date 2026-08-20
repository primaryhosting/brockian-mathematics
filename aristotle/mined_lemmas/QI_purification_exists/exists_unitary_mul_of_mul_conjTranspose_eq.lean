/-
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Every mixed state has a purification, unique up to a unitary on the ancilla.

A mixed state on an `n`-dimensional Hilbert space `H` is a positive semidefinite matrix `ρ`
of trace one.  A pure state of the composite system `H ⊗ K`, with `K` an `m`-dimensional
ancilla, is encoded by its matrix of coefficients `psi : Matrix (Fin n) (Fin m) ℂ` in the
product basis, and the partial trace over the ancilla is `reducedDensity psi = psi * psiᴴ`.

The uniqueness statement is the operator fact `A Aᴴ = B Bᴴ → ∃ U unitary, B = A U`, which we
derive from `LinearIsometry.extend`: the assignment `Aᴴ x ↦ Bᴴ x` is a well-defined isometry
on `range Aᴴ` and extends to an isometry of the whole space.
-/

open Matrix

open scoped ComplexOrder MatrixOrder

namespace QI

noncomputable section

/-- The reduced density matrix (partial trace over the ancilla) of the pure state `|ψ⟩⟨ψ|`,
where the vector `ψ` of the composite system `H ⊗ K` (`H` of dimension `n`, ancilla `K` of
dimension `m`) is encoded by its coefficient matrix `psi` in the product basis,
`ψ = ∑ i, ∑ j, psi i j • (e i ⊗ f j)`. -/

theorem exists_unitary_mul_of_mul_conjTranspose_eq (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : A * Aᴴ = B * Bᴴ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ B = A * U := by
  have hadjA : LinearMap.adjoint (Matrix.toEuclideanLin A) = Matrix.toEuclideanLin Aᴴ :=
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
  have hadjB : LinearMap.adjoint (Matrix.toEuclideanLin B) = Matrix.toEuclideanLin Bᴴ :=
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint B).symm
  have h' : Matrix.toEuclideanLin A ∘ₗ LinearMap.adjoint (Matrix.toEuclideanLin A)
      = Matrix.toEuclideanLin B ∘ₗ LinearMap.adjoint (Matrix.toEuclideanLin B) := by
    rw [hadjA, hadjB, ← toEuclideanLin_mul, ← toEuclideanLin_mul, h]
  obtain ⟨W, hW⟩ := exists_isometry_of_comp_adjoint_eq h'
  set M := Matrix.toEuclideanLin.symm (W.toLinearMap) with hM
  have hMlin : Matrix.toEuclideanLin M = W.toLinearMap := LinearEquiv.apply_symm_apply _ _
  have hMA : M * Aᴴ = Bᴴ := by
    apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul, hMlin, ← hadjA, ← hadjB]
    exact LinearMap.ext hW
  have hMM : Mᴴ * M = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul, toEuclideanLin_one, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      hMlin, adjoint_comp_self_of_isometry]
  refine ⟨Mᴴ, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    simpa [Matrix.star_eq_conjTranspose] using mul_eq_one_comm.mp hMM
  · have hcong := congrArg Matrix.conjTranspose hMA
    simpa [Matrix.conjTranspose_mul] using hcong.symm

end MatrixLin

/-- Existence of a purification: a positive semidefinite `ρ` is `psi * psiᴴ` for some `psi`. -/
