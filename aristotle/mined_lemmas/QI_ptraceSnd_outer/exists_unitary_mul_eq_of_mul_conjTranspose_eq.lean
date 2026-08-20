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

theorem exists_unitary_mul_eq_of_mul_conjTranspose_eq {psi phi : Matrix n m ℂ}
    (h : psi * psiᴴ = phi * phiᴴ) : ∃ U ∈ Matrix.unitaryGroup m ℂ, psi * U = phi := by
  obtain ⟨W, hW, hWA⟩ := exists_unitary_mul_eq_of_conjTranspose_mul_eq
    (A := psiᴴ) (B := phiᴴ) (by simpa using h)
  refine ⟨Wᴴ, ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hW
  · have := congrArg Matrix.conjTranspose hWA
    simpa [Matrix.conjTranspose_mul] using this

/-! ### Main theorem -/

/-- **Purification.**  Every mixed state `rho` has a purification with ancilla of the same
dimension, and any two purifications (with the same ancilla) are related by a unitary acting
on the ancilla only. -/
