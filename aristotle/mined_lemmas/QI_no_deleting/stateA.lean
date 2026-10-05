/-
/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
## Formalization

We work with a single qubit `Qubit = EuclideanSpace ℂ (Fin 2)` and the two-qubit space
`Qubit2 = EuclideanSpace ℂ (Fin 2 × Fin 2)`, with the product state `tens x y` given by
`(x ⊗ y) (i, j) = x i * y j`.

A *deleting machine* would be a unitary `U` on the two-qubit space together with a fixed
blank state `s` (a unit vector) such that `U (x ⊗ x) = x ⊗ s` for every unit vector `x`,
i.e. the second copy of the unknown state `x` is erased and replaced by a state that does
not depend on `x`.  The no-deleting theorem says no such unitary exists: unitaries preserve
inner products, so `⟪x, y⟫ ^ 2 = ⟪x, y⟫ ⟪s, s⟫ = ⟪x, y⟫` for all unit `x, y`, which fails
for e.g. `x = (1, 0)` and `y = (3/5, 4/5)`.
-/

namespace QI

open scoped InnerProductSpace ComplexConjugate

/-- The state space of one qubit. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The state space of two qubits. -/
abbrev Qubit2 := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The product (tensor) state `x ⊗ y`. -/

def stateA : Qubit := WithLp.toLp 2 ![1, 0]

/-- Another unit vector, not orthogonal to `stateA` and different from it. -/
