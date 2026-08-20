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

/-- The state space of 8 qubits: the (finite-dimensional) complex Hilbert space with orthonormal
basis indexed by bit strings `Fin 8 → Bool`. -/
abbrev Qubits8 : Type := EuclideanSpace ℂ (Fin 8 → Bool)

/-- The computational basis state `|x⟩` for a bit string `x : Fin 8 → Bool`. -/

theorem allFalse_ne_allTrue : (fun _ : Fin 8 => false) ≠ (fun _ : Fin 8 => true) := by
  intro h
  have := congrFun h 0
  simp at this

/-- The coordinates of the GHZ state: `1/√2` at `|0…0⟩` and at `|1…1⟩`, and `0` elsewhere. -/
