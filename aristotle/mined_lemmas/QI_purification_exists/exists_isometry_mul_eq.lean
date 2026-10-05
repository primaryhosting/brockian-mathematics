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

theorem exists_isometry_mul_eq {m' : Type*} [Fintype n] [Fintype m] [Fintype m'] [DecidableEq n]
    [DecidableEq m] [DecidableEq m'] {A : Matrix n m ℂ} {B : Matrix n m' ℂ}
    (h : A * Aᴴ = B * Bᴴ) (hcard : Fintype.card m ≤ Fintype.card m') :
    ∃ V : Matrix m m' ℂ, V * Vᴴ = 1 ∧ B = A * V := by
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  set E : Matrix m m' ℂ := (1 : Matrix m' m' ℂ).submatrix ι id with hE
  have hEE : E * Eᴴ = 1 := by
    ext k l
    simp [hE, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, Finset.sum_ite_eq',
      ι.injective.eq_iff, eq_comm]
  have h' : (A * E) * (A * E)ᴴ = B * Bᴴ := by
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc A E, hEE,
      Matrix.mul_one, h]
  obtain ⟨U, hUmem, hU⟩ := exists_unitary_mul_eq h'
  have hUU : U * Uᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff (A := U)).mp hUmem
  refine ⟨E * U, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc E U, hUU,
      Matrix.mul_one, hEE]
  · rw [hU, Matrix.mul_assoc]

/-! ### Purification -/

/-- **Existence of purifications.** Every mixed state `ρ` on `H_A` (a positive semidefinite
matrix of trace one) has a purification by a unit vector of `H_A ⊗ H_A`. -/
