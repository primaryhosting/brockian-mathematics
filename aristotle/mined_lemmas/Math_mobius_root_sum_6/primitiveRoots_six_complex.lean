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

namespace Math

open ArithmeticFunction

/-- One of the two primitive 6-th roots of unity, `exp (π i / 3) = (1 + i √3) / 2`. -/

lemma primitiveRoots_six_complex : primitiveRoots 6 ℂ = {zeta6, zeta6'} := by
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).mpr isPrimitiveRoot_zeta6
    · exact (mem_primitiveRoots (by norm_num)).mpr isPrimitiveRoot_zeta6'
  · rw [isPrimitiveRoot_zeta6.card_primitiveRoots, Finset.card_insert_of_notMem (by
      simpa using zeta6_ne_zeta6'), Finset.card_singleton]
    decide +kernel

/-- The sum of the primitive 6-th roots of unity equals `μ 6`. -/
