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

open Polynomial Finset

namespace Math

/-- A concrete primitive 11-th root of unity in `ℂ`. -/

theorem nthRootsFinset_11_eq_insert :
    nthRootsFinset 11 (1 : ℂ) = insert 1 (primitiveRoots 11 ℂ) := by
  rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots (R := ℂ) (n := 11)]
  have h : Nat.divisors 11 = {1, 11} := by decide
  rw [h]
  simp [IsPrimitiveRoot.primitiveRoots_one]

/-- The sum of the primitive 11-th roots of unity equals `μ 11 = -1`. -/
