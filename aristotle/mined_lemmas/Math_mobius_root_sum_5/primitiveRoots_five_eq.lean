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

open Finset

namespace Math

/-- A fixed primitive 5-th root of unity in `ℂ`. -/

lemma primitiveRoots_five_eq :
    primitiveRoots 5 ℂ = (Finset.Ico 1 5).image (fun i : ℕ => Math.zeta5 ^ i) := by
  have h := Math.isPrimitiveRoot_zeta5
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_Ico] at hx
    obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := hx
    rw [mem_primitiveRoots (by norm_num)]
    refine h.pow_of_coprime i ?_
    have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> decide
  · rw [Complex.card_primitiveRoots, Finset.card_image_of_injOn Math.zeta5_pow_injOn,
      Nat.card_Ico]
    decide

/-- The sum of the primitive 5-th roots of unity equals the Möbius function `μ(5) = -1`. -/
