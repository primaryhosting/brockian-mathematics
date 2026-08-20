/-
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Statement: There is no unitary that deletes an unknown quantum state (no-deleting theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexConjugate

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-- A qubit: the two-dimensional complex Hilbert space. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The register of a deleting machine: two qubits together with an ancilla indexed by `ι`.
Concretely this is the Hilbert space `ℂ^(2 × 2 × ι)`, which is the tensor product of two
qubit spaces with the ancilla space `ℂ^ι`. -/
abbrev Register (ι : Type) : Type := EuclideanSpace ℂ (Fin 2 × Fin 2 × ι)

/-- The product (tensor) state `x ⊗ y ⊗ a` of two qubits and an ancilla. -/

theorem norm_eq_one_of_inner_self {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {x : E} (h : inner ℂ x x = (1 : ℂ)) : ‖x‖ = 1 := by
  have h2 : ((‖x‖ : ℂ)) ^ 2 = (1 : ℂ) := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x).symm.trans h
  have h3 : (‖x‖ : ℝ) ^ 2 = 1 := by exact_mod_cast h2
  nlinarith [norm_nonneg x]

/-- The self-inner-product of a unit vector is `1`. -/
