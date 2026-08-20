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

theorem purification_exists {n : Type*} [Fintype n] [DecidableEq n]
    (rho : Matrix n n ℂ) (hrho : IsMixedState rho) :
    (∃ v : n × n → ℂ, IsPurification rho v) ∧
      ∀ v w : n × n → ℂ, IsPurification rho v → IsPurification rho w →
        ∃ U ∈ Matrix.unitaryGroup n ℂ, ∀ i k, w (i, k) = ∑ l, U k l * v (i, l) := by
  constructor
  · refine ⟨fun p => CFC.sqrt rho p.1 p.2, ?_⟩
    have hsqrt : (CFC.sqrt rho).PosSemidef := (CFC.sqrt_nonneg rho).posSemidef
    show ptraceSnd (outer _) = rho
    rw [ptraceSnd_outer]
    have hre : reshape (fun p : n × n => CFC.sqrt rho p.1 p.2) = CFC.sqrt rho := rfl
    rw [hre, hsqrt.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self rho (ha := hrho.posSemidef.nonneg)
  · intro v w hv hw
    have h : reshape v * (reshape v)ᴴ = reshape w * (reshape w)ᴴ := by
      rw [← ptraceSnd_outer, ← ptraceSnd_outer, hv, hw]
    obtain ⟨U, hU, hUeq⟩ := exists_unitary_mul_eq_of_mul_conjTranspose_eq h
    refine ⟨Uᵀ, ?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff] at hU
      rw [Matrix.mem_unitaryGroup_iff']
      have hst : star (Uᵀ) = (star U)ᵀ := by
        ext i j; simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
      rw [hst, ← Matrix.transpose_mul, hU, Matrix.transpose_one]
    · intro i k
      have := congrFun (congrFun hUeq i) k
      simpa [reshape, Matrix.mul_apply, mul_comm] using this.symm

/-- **Uniqueness up to an isometry on the ancilla**, for purifications with ancillas of
different dimensions:  if `v` (ancilla `m`) and `w` (ancilla `m'`) both purify `rho`, and the
ancilla of `w` is at least as large, then `w = (1 ⊗ S) v` for an isometry `S` (i.e. `Sᴴ S = 1`)
acting on the ancilla alone. -/
