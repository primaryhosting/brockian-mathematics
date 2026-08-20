import Mathlib

set_option maxHeartbeats 1000000

/-!
# Purification of mixed states

A mixed state on a finite dimensional system `n` is a positive semidefinite matrix `rho` of
trace one.  A *purification* of `rho` is a unit vector `psi` on the composite system
`n × m` (system ⊗ ancilla) whose reduced density matrix (partial trace over the ancilla `m`)
is `rho`.

The main theorem `QI.purification_exists` states that

* every mixed state admits a purification (with ancilla a copy of the system), and
* any two purifications of the same mixed state are related by an isometry acting on the
  ancilla alone (in particular, for ancillas of the same dimension, by a unitary).
-/

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

section Defs

variable {n m : Type*}

/-- The matrix `A` whose `(i,k)` entry is `psi (i,k)`; this is the standard identification of a
vector of the composite system `n × m` with a linear map. -/

theorem exists_isometry_of_mul_conjTranspose_eq {n m₁ m₂ : Type*} [Fintype n] [DecidableEq n]
    [Fintype m₁] [DecidableEq m₁] [Fintype m₂] [DecidableEq m₂]
    (A : Matrix n m₁ ℂ) (B : Matrix n m₂ ℂ) (h : A * Aᴴ = B * Bᴴ)
    (hcard : Fintype.card m₁ ≤ Fintype.card m₂) :
    ∃ W : Matrix m₂ m₁ ℂ, Wᴴ * W = 1 ∧ B = A * Wᴴ := by
  obtain ⟨j⟩ : Nonempty (m₁ ↪ m₂) := Function.Embedding.nonempty_of_card_le hcard
  set J : Matrix m₂ m₁ ℂ := Matrix.of (fun k l => if k = j l then 1 else 0) with hJ
  have hJiso : Jᴴ * J = 1 := by
    ext l l'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hJ, Matrix.of_apply,
      Matrix.one_apply]
    rw [Finset.sum_eq_single (j l)]
    · by_cases hll' : l = l'
      · subst hll'; simp
      · simp [hll']
    · intro k _ hk
      simp [hk]
    · simp
  obtain ⟨U, hU, hBU⟩ := exists_unitary_of_mul_conjTranspose_eq (A * Jᴴ) B (by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← h,
      Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ J Aᴴ, hJiso, Matrix.one_mul])
  refine ⟨Uᴴ * J, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc U Uᴴ J, mul_eq_one_comm.mp hU, Matrix.one_mul, hJiso]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, hBU]

/-- Every positive semidefinite matrix of trace one is of the form `A Aᴴ` for a matrix `A` whose
entries have squared norms summing to one. -/
