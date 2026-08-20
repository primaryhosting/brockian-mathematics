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

/-- A qubit state: a vector of amplitudes indexed by the computational basis `{0,1}`. -/
abbrev Qubit := Fin 2 → ℂ

/-- The Pauli `X` (bit flip) gate. -/

@[simp] lemma pauliZp_one : pauliZp 1 = pauliZ := by
  funext v c; simp [pauliZp, pauliZ]

/-- The four Bell states form an orthonormal basis of the two-qubit space, so measuring in
this basis is a genuine projective measurement. -/
