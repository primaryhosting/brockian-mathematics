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

theorem nthRootsFinset_11_eq_image :
    nthRootsFinset 11 (1 : ℂ) = Finset.image (fun i => zeta11 ^ i) (Finset.range 11) := by
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Polynomial.mem_nthRootsFinset (by norm_num), ← pow_mul, mul_comm, pow_mul,
      isPrimitiveRoot_zeta11.pow_eq_one, one_pow]
  · rw [isPrimitiveRoot_zeta11.card_nthRootsFinset]
    refine le_trans (le_of_eq (by simp)) (le_of_eq (Finset.card_image_of_injOn ?_).symm)
    intro a ha b hb hab
    exact isPrimitiveRoot_zeta11.pow_inj (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab

/-- The sum of all 11-th roots of unity vanishes. -/
