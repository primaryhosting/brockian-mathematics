import Mathlib

/-!
# Purification of mixed states

A *mixed state* on a finite-dimensional system with index type `n` is a positive semidefinite
matrix `rho : Matrix n n ℂ` of trace `1`.  A *purification* of `rho` with ancilla index type `m`
is a vector `v : n × m → ℂ` in the tensor product whose density matrix `|v⟩⟨v|` has partial
trace over the ancilla equal to `rho`.

The main result `QI.purification_exists` states that every mixed state admits a purification
(with ancilla of the same dimension), and that any two purifications with the same ancilla
differ by a unitary acting on the ancilla alone.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder

set_option synthInstance.maxHeartbeats 1000000

namespace QI

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The density matrix `|v⟩⟨v|` of the vector `v`. -/

theorem purification_unique_up_to_isometry {n m m' : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (hcard : Fintype.card m ≤ Fintype.card m')
    (rho : Matrix n n ℂ) (v : n × m → ℂ) (w : n × m' → ℂ)
    (hv : IsPurification rho v) (hw : IsPurification rho w) :
    ∃ S : Matrix m' m ℂ, Sᴴ * S = 1 ∧ ∀ i k, w (i, k) = ∑ l, S k l * v (i, l) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  set P : Matrix m m' ℂ := (1 : Matrix m' m' ℂ).submatrix e id with hPdef
  have hPP : P * Pᴴ = 1 := by
    ext i j
    by_cases hij : i = j <;>
      simp [hPdef, Matrix.mul_apply, Matrix.one_apply,
        e.injective.eq_iff, hij, eq_comm, Finset.sum_ite_eq']
  have hgram : (reshape v * P) * (reshape v * P)ᴴ = reshape w * (reshape w)ᴴ := by
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (reshape v), hPP,
      Matrix.mul_one, ← ptraceSnd_outer, ← ptraceSnd_outer, hv, hw]
  obtain ⟨U, hU, hUeq⟩ := exists_unitary_mul_eq_of_mul_conjTranspose_eq hgram
  refine ⟨(P * U)ᵀ, ?_, ?_⟩
  · have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
    have h1 : (P * U) * (P * U)ᴴ = 1 := by
      rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc P, hUU,
        Matrix.mul_one, hPP]
    have h3 : ((P * U)ᵀ)ᴴ = ((P * U)ᴴ)ᵀ := rfl
    rw [h3, ← Matrix.transpose_mul, h1, Matrix.transpose_one]
  · intro i k
    have := congrFun (congrFun hUeq i) k
    rw [Matrix.mul_assoc] at this
    simpa [reshape, Matrix.mul_apply, mul_comm] using this.symm

/-! ### Sanity check -/

/-- The Bell state `(|00⟩ + |11⟩)/√2` is a purification of the maximally mixed qubit state. -/
