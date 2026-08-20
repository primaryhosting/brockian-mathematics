import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Statement: Every mixed state has a purification, unique up to isometry on the ancilla.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

/-!
## Setting

A state of a finite dimensional quantum system with basis indexed by `n` is a positive
semidefinite matrix `ρ : Matrix n n ℂ` of trace one.

A vector of the composite system `H ⊗ K`, where `K` is an ancilla with basis indexed by `m`,
is encoded by its matrix of coefficients `A : Matrix n m ℂ`, i.e. `A` encodes
`∑ i, ∑ j, A i j • (e i ⊗ f j)`.  With this encoding the reduced density matrix
(the partial trace over the ancilla) of the pure state `|A⟩⟨A|` is exactly `A * Aᴴ`, and the
squared norm of the vector is `∑ i, ∑ j, ‖A i j‖ ^ 2 = trace (A * Aᴴ)`.

Consequently `A` purifies `ρ` exactly when `A * Aᴴ = ρ`, and an isometry `K → K'` of ancillas
acting on the second tensor factor sends the vector `A` to `A * W`, where `W : Matrix m m' ℂ`
satisfies `W * Wᴴ = 1`.
-/

/-- `A` is a purification of the state `ρ`: the reduced density matrix (partial trace over the
ancilla) of the pure state given by the vector with coefficient matrix `A` equals `ρ`. -/

theorem purification_unique {n m m' : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] [Fintype m'] [DecidableEq m'] {ρ : Matrix n n ℂ}
    (A : Matrix n m ℂ) (B : Matrix n m' ℂ) (hA : IsPurification ρ A) (hB : IsPurification ρ B)
    (hcard : Fintype.card m ≤ Fintype.card m') :
    ∃ W : Matrix m m' ℂ, W * Wᴴ = 1 ∧ A * W = B := by
  obtain ⟨J, hJ⟩ := exists_isometry_matrix (m := m) (m' := m') hcard
  have hA' : (A * Jᴴ) * (A * Jᴴ)ᴴ = B * Bᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc,
      Matrix.mul_assoc A Jᴴ J, hJ, Matrix.mul_one, hA, hB]
  obtain ⟨U, hU, hAU⟩ := exists_unitary_mul_eq (A * Jᴴ) B hA'
  refine ⟨Jᴴ * U, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc U Uᴴ J, hU, Matrix.one_mul, hJ]
  · rw [← Matrix.mul_assoc, hAU]

/-- **Every mixed state has a purification, unique up to an isometry on the ancilla.**

Let `ρ` be a mixed state of a finite dimensional system (a positive semidefinite matrix of
trace one).  Then:

* (existence) there is a purification `A` of `ρ` using an ancilla of the same dimension as the
  system, and the corresponding vector of the composite system is a unit vector;
* (uniqueness) any two purifications `A` (ancilla `m`) and `B` (ancilla `m'`) of `ρ` with
  `card m ≤ card m'` are related by an isometry `W` on the ancilla, `W * Wᴴ = 1`, via
  `A * W = B`.
-/
