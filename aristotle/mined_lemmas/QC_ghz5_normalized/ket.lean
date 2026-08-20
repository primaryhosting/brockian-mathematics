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

/-- The computational-basis ket `|x⟩` for a 5-bit string `x`, as a vector in the
5-qubit state space `ℂ^(2^5)`, modelled as `EuclideanSpace ℂ (Fin 5 → Fin 2)`. -/

noncomputable def ket (x : Fin 5 → Fin 2) : EuclideanSpace ℂ (Fin 5 → Fin 2) :=
  EuclideanSpace.single x 1

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`. -/
