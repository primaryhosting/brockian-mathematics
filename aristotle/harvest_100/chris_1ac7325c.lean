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
noncomputable def zeta9 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)

lemma isPrimitiveRoot_zeta9 : IsPrimitiveRoot zeta9 9 :=
  Complex.isPrimitiveRoot_exp 9 (by norm_num)

/-- The set of primitive 9-th roots of unity in `ℂ` consists of the powers `ζ ^ k`
for `k ∈ {1, 2, 4, 5, 7, 8}`, where `ζ = exp (2 π i / 9)`. -/
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

lemma not_squarefree_nine : ¬ Squarefree (9 : ℕ) := by
  intro h
  have h3 := h 3 (by norm_num)
  rw [Nat.isUnit_iff] at h3
  omega

/-- **Mobius Root Sum 9**: the sum of the primitive 9-th roots of unity in `ℂ`
equals `μ 9` (which is `0`, since `9` is not squarefree). -/
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

