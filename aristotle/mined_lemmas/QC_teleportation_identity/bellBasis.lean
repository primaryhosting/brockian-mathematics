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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-! ## Quantum teleportation

A single qubit is a vector in `ℂ²`, represented as `Fin 2 → ℂ`.
Multi-qubit states are represented by their coefficient functions on the
computational basis (so a three-qubit state is `Fin 2 → Fin 2 → Fin 2 → ℂ`).
Addition on `Fin 2` is addition mod 2, i.e. the XOR of classical bits.
-/

/-- A one-qubit state vector, given by its coefficients in the basis `|0⟩, |1⟩`. -/
abbrev Qubit : Type := Fin 2 → ℂ

/-- The scalar `1/√2`. -/

noncomputable def bellBasis (m₁ m₂ : Fin 2) : Fin 2 → Fin 2 → ℂ :=
  fun i j => if j = i + m₂ then invSqrt2 * (-1 : ℂ) ^ ((m₁ : ℕ) * (i : ℕ)) else 0

/-- The four states `|β_{m₁m₂}⟩` form an orthonormal basis of the two-qubit space. -/
