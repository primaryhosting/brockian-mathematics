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

/-- The amplitude function of the 6-qubit GHZ state
`(|000000⟩ + |111111⟩)/√2`: a computational basis state `x : Fin 6 → Fin 2`
gets amplitude `1/√2` if it is all-zeros or all-ones, and `0` otherwise. -/

noncomputable def ghz6Fun : (Fin 6 → Fin 2) → ℂ :=
  fun x =>
    if x = (fun _ => 0) then (1 : ℂ) / (Real.sqrt 2 : ℂ)
    else if x = (fun _ => 1) then (1 : ℂ) / (Real.sqrt 2 : ℂ)
    else 0

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, as a vector in the
`2^6`-dimensional complex Hilbert space indexed by the bit strings `Fin 6 → Fin 2`. -/
