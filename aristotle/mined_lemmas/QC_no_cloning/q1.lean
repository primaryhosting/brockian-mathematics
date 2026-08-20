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

/-!
# The no-cloning theorem

We work with a single qubit space `QC.H := EuclideanSpace ℂ (Fin 2)` and model the
two-fold tensor product `H ⊗ H` concretely as `QC.HH := EuclideanSpace ℂ (Fin 2 × Fin 2)`,
with the elementary tensor `QC.tens a b` given by `(a ⊗ b) (i, j) = a i * b j`.
This satisfies the defining property of the tensor inner product,
`⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ * ⟪b, d⟫` (see `QC.inner_tens`).

The main results state that there is no unitary `U` on `H ⊗ H` with
`U (ψ ⊗ |0⟩) = ψ ⊗ ψ` for every unit vector `ψ`, both for `U` a linear isometry
equivalence (`QC.no_cloning`) and for `U` a unitary element of the algebra of
continuous linear operators (`QC.no_cloning_unitary`).
-/

namespace QC

/-- The state space of one qubit. -/
abbrev H : Type := EuclideanSpace ℂ (Fin 2)

/-- The state space of two qubits, i.e. `H ⊗ H`. -/
abbrev HH : Type := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The elementary tensor `a ⊗ b` of two qubit states. -/

noncomputable def q1 : H := EuclideanSpace.single 1 1

/-- The state `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
