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

theorem deleting_moves_state_to_ancilla {ι : Type} [Fintype ι]
    (a : EuclideanSpace ℂ ι) (ha : ‖a‖ = 1)
    (A : Qubit → EuclideanSpace ℂ ι)
    (U : Register ι ≃ₗᵢ[ℂ] Register ι)
    (hU : ∀ x : Qubit, ‖x‖ = 1 → U (tens3 x x a) = tens3 x ket0 (A x))
    (x y : Qubit) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hne : inner ℂ x y ≠ 0) :
    inner ℂ (A x) (A y) = inner ℂ x y := by
  have key : inner ℂ (U (tens3 x x a)) (U (tens3 y y a)) = inner ℂ (tens3 x x a) (tens3 y y a) :=
    U.inner_map_map _ _
  rw [hU x hx, hU y hy, inner_tens3, inner_tens3, inner_self_of_norm_eq_one ha,
    inner_ket0_ket0] at key
  have key' : inner ℂ x y * inner ℂ (A x) (A y) = inner ℂ x y * inner ℂ x y := by
    linear_combination key
  exact mul_left_cancel₀ hne key'

/-- **No-deleting theorem.**  There is no unitary that deletes an unknown quantum state:
no unitary `U` on two qubits plus an ancilla (initialised in a unit state `a`) can map
`|x⟩|x⟩|a⟩` to `|x⟩|0⟩|anc⟩` for every unit qubit state `x`, with a final ancilla state `anc`
that does not depend on `x`. -/
