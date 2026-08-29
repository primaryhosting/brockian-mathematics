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

theorem mobius_root_sum_9 :
    ∑ z ∈ primitiveRoots 9 ℂ, z = (ArithmeticFunction.moebius 9 : ℤ) := by
  have hζ := isPrimitiveRoot_zeta9
  have hinj : Set.InjOn (fun k : ℕ => zeta9 ^ k) ({1, 2, 4, 5, 7, 8} : Finset ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at ha hb
    have ha9 : a < 9 := by rcases ha with h | h | h | h | h | h <;> omega
    have hb9 : b < 9 := by rcases hb with h | h | h | h | h | h <;> omega
    exact (hζ.pow_inj ha9 hb9) hab
  have hsum9 : ∑ i ∈ Finset.range 9, zeta9 ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hcube : IsPrimitiveRoot (zeta9 ^ 3) 3 := hζ.pow (by norm_num) (show 9 = 3 * 3 by norm_num)
  have hsum3 : ∑ i ∈ Finset.range 3, (zeta9 ^ 3) ^ i = 0 := hcube.geom_sum_eq_zero (by norm_num)
  have hmu : (ArithmeticFunction.moebius 9 : ℤ) = 0 := by
    simp [ArithmeticFunction.moebius, not_squarefree_nine]
  rw [primitiveRoots_nine_eq_image, Finset.sum_image (fun a ha b hb h => hinj ha hb h), hmu]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum9 hsum3
  norm_num
  linear_combination hsum9 - hsum3

end Math

