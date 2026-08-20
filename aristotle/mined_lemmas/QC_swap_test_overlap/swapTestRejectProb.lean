import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open scoped ComplexConjugate

namespace QC

variable {d : ℕ}

/-- Index type for the three registers used in the SWAP test: a one-qubit
ancilla (`Fin 2`) together with two `d`-dimensional data registers.  A state of
the whole system is a complex amplitude function on this index type. -/
abbrev Reg (d : ℕ) : Type := Fin 2 × Fin d × Fin d

/-- The initial state of the SWAP test, `|0⟩ ⊗ |ψ⟩ ⊗ |ϕ⟩`. -/

noncomputable def swapTestRejectProb (ψ ϕ : Fin d → ℂ) : ℝ :=
  ∑ q : Fin d × Fin d, ‖swapTestState ψ ϕ (1, q)‖ ^ 2

/-- For unit vectors `ψ` and `ϕ`, the SWAP test rejects (measures `1` on the
ancilla) with probability `(1 - |⟨ψ|ϕ⟩|²)/2`. -/
