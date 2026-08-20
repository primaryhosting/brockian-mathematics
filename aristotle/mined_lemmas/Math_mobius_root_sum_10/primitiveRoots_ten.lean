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

/-- A fixed primitive 10-th root of unity in `ℂ`. -/

theorem primitiveRoots_ten :
    primitiveRoots 10 ℂ = {zeta10, zeta10 ^ 3, zeta10 ^ 7, zeta10 ^ 9} := by
  have hcard : ({zeta10, zeta10 ^ 3, zeta10 ^ 7, zeta10 ^ 9} : Finset ℂ).card = 4 := by
    rw [Finset.card_insert_of_notMem zeta10_notMem_one,
      Finset.card_insert_of_notMem zeta10_notMem_three,
      Finset.card_insert_of_notMem zeta10_notMem_seven, Finset.card_singleton]
  have hsub : ({zeta10, zeta10 ^ 3, zeta10 ^ 7, zeta10 ^ 9} : Finset ℂ) ⊆ primitiveRoots 10 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_primitiveRoots (by norm_num)]
    rcases hx with rfl | rfl | rfl | rfl
    · exact isPrimitiveRoot_zeta10
    · exact isPrimitiveRoot_zeta10.pow_of_coprime 3 (by norm_num)
    · exact isPrimitiveRoot_zeta10.pow_of_coprime 7 (by norm_num)
    · exact isPrimitiveRoot_zeta10.pow_of_coprime 9 (by norm_num)
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Complex.card_primitiveRoots, hcard, show Nat.totient 10 = 4 from by decide]

