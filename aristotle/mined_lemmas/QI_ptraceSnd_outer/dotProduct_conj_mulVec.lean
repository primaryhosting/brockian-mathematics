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

private lemma dotProduct_conj_mulVec {p q : Type*} [Fintype p] [Fintype q]
    (A : Matrix p q ℂ) (x y : q → ℂ) :
    star (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = star x ⬝ᵥ ((Aᴴ * A) *ᵥ y) := by
  rw [star_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul]

