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

noncomputable def ptraceSnd (M : Matrix (n × m) (n × m) ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => ∑ k, M (i, k) (j, k)

/-- A mixed state is a positive semidefinite matrix of unit trace. -/
structure IsMixedState (rho : Matrix n n ℂ) : Prop where
  posSemidef : rho.PosSemidef
  trace_one : rho.trace = 1

/-- `v : n × m → ℂ` is a purification of the state `rho` if tracing out the ancilla `m`
from the pure state `|v⟩⟨v|` gives back `rho`. -/
