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

namespace Frontier

variable (c : ℕ → ℕ → Bool)

open Classical in
/-- The colour chosen at a stage of the Ramsey construction: `true` if the set of elements of
`S` above `sInf S` that are joined to `sInf S` in colour `true` is infinite, `false` otherwise. -/

lemma sInf_lt_of_mem_ramseyNext {S : Set ℕ} {x : ℕ} (hx : x ∈ ramseyNext c S) :
    sInf S < x := hx.2.1

