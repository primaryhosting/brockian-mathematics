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

/-
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Math

/-- A fixed primitive 9-th root of unity in `ℂ`. -/

lemma primitiveRoots_nine_eq_image :
    primitiveRoots 9 ℂ = ({1, 2, 4, 5, 7, 8} : Finset ℕ).image (fun k => zeta9 ^ k) := by
  have hζ := isPrimitiveRoot_zeta9
  ext x
  simp only [mem_primitiveRoots (by norm_num : 0 < 9), Finset.mem_image, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx.pow_eq_one
    have hcop : Nat.Coprime i 9 := (hζ.pow_iff_coprime (by norm_num) i).mp hx
    refine ⟨i, ?_, rfl⟩
    interval_cases i <;> revert hcop <;> decide
  · rintro ⟨i, hi, rfl⟩
    have hcop : Nat.Coprime i 9 := by
      rcases hi with h | h | h | h | h | h <;> subst h <;> decide
    exact hζ.pow_of_coprime i hcop

