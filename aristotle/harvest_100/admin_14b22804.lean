import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Complex

namespace Math

/-- One primitive 6-th root of unity: `1/2 + (√3/2) i`. -/
noncomputable def zeta6 : ℂ := 1 / 2 + (Real.sqrt 3 / 2) * Complex.I

/-- The other primitive 6-th root of unity: `1/2 - (√3/2) i`. -/
noncomputable def zeta6' : ℂ := 1 / 2 - (Real.sqrt 3 / 2) * Complex.I

lemma sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  have : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) this

lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

lemma zeta6_im : zeta6.im = Real.sqrt 3 / 2 := by
  simp [zeta6]

lemma zeta6'_im : zeta6'.im = -(Real.sqrt 3 / 2) := by
  simp [zeta6']

lemma zeta6_ne_real (r : ℝ) : zeta6 ≠ (r : ℂ) := by
  intro h
  have := congrArg Complex.im h
  rw [zeta6_im] at this
  simp at this

lemma zeta6'_ne_real (r : ℝ) : zeta6' ≠ (r : ℂ) := by
  intro h
  have := congrArg Complex.im h
  rw [zeta6'_im] at this
  simp at this

lemma zeta6_sq : zeta6 ^ 2 = zeta6 - 1 := by
  simp only [zeta6]
  linear_combination (Complex.I ^ 2 / 4) * sqrt3_sq + (3 / 4 : ℂ) * Complex.I_sq

lemma zeta6'_sq : zeta6' ^ 2 = zeta6' - 1 := by
  simp only [zeta6']
  linear_combination (Complex.I ^ 2 / 4) * sqrt3_sq + (3 / 4 : ℂ) * Complex.I_sq

lemma zeta6_cube : zeta6 ^ 3 = -1 := by
  linear_combination (zeta6 + 1) * zeta6_sq

lemma zeta6'_cube : zeta6' ^ 3 = -1 := by
  linear_combination (zeta6' + 1) * zeta6'_sq

lemma zeta6_pow_six : zeta6 ^ 6 = 1 := by
  linear_combination (zeta6 ^ 3 - 1) * zeta6_cube

lemma zeta6'_pow_six : zeta6' ^ 6 = 1 := by
  linear_combination (zeta6' ^ 3 - 1) * zeta6'_cube

lemma zeta6_pow_four : zeta6 ^ 4 = -zeta6 := by
  linear_combination zeta6 * zeta6_cube

lemma zeta6_pow_five : zeta6 ^ 5 = 1 - zeta6 := by
  linear_combination zeta6 ^ 2 * zeta6_cube - zeta6_sq

lemma zeta6'_pow_four : zeta6' ^ 4 = -zeta6' := by
  linear_combination zeta6' * zeta6'_cube

lemma zeta6'_pow_five : zeta6' ^ 5 = 1 - zeta6' := by
  linear_combination zeta6' ^ 2 * zeta6'_cube - zeta6'_sq

lemma isPrimitiveRoot_zeta6 : IsPrimitiveRoot zeta6 6 := by
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) zeta6_pow_six ?_
  intro l hl hl6 h
  interval_cases l
  · exact zeta6_ne_real 1 (by simpa using h)
  · exact zeta6_ne_real 2 (by push_cast; linear_combination h - zeta6_sq)
  · rw [zeta6_cube] at h; norm_num at h
  · exact zeta6_ne_real (-1) (by push_cast; linear_combination zeta6_pow_four - h)
  · exact zeta6_ne_real 0 (by push_cast; linear_combination zeta6_pow_five - h)

lemma isPrimitiveRoot_zeta6' : IsPrimitiveRoot zeta6' 6 := by
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) zeta6'_pow_six ?_
  intro l hl hl6 h
  interval_cases l
  · exact zeta6'_ne_real 1 (by simpa using h)
  · exact zeta6'_ne_real 2 (by push_cast; linear_combination h - zeta6'_sq)
  · rw [zeta6'_cube] at h; norm_num at h
  · exact zeta6'_ne_real (-1) (by push_cast; linear_combination zeta6'_pow_four - h)
  · exact zeta6'_ne_real 0 (by push_cast; linear_combination zeta6'_pow_five - h)

lemma zeta6_ne_zeta6' : zeta6 ≠ zeta6' := by
  intro h
  have := congrArg Complex.im h
  rw [zeta6_im, zeta6'_im] at this
  linarith [sqrt3_pos]

lemma zeta6_add_zeta6' : zeta6 + zeta6' = 1 := by
  simp only [zeta6, zeta6']
  ring

lemma zeta6_mul_zeta6' : zeta6 * zeta6' = 1 := by
  simp only [zeta6, zeta6']
  linear_combination (-(Complex.I ^ 2) / 4) * sqrt3_sq - (3 / 4 : ℂ) * Complex.I_sq

/-- A complex number is a primitive 6-th root of unity iff it is `zeta6` or `zeta6'`. -/
lemma primitiveRoots_six : primitiveRoots 6 ℂ = {zeta6, zeta6'} := by
  ext x
  rw [mem_primitiveRoots (by norm_num), Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have h6 : x ^ 6 = 1 := h.pow_eq_one
    have h2 : x ^ 2 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have h3 : x ^ 3 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have hx1 : x + 1 ≠ 0 := by
      intro hx
      apply h2
      have hx' : x = -1 := by linear_combination hx
      rw [hx']; norm_num
    have key : (x ^ 3 - 1) * ((x + 1) * (x ^ 2 - x + 1)) = 0 := by linear_combination h6
    have hq : x ^ 2 - x + 1 = 0 := by
      rcases mul_eq_zero.mp key with h' | h'
      · exact absurd (by linear_combination h' : x ^ 3 = 1) h3
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' hx1
        · exact h''
    have : (x - zeta6) * (x - zeta6') = 0 := by
      linear_combination hq + (-x) * zeta6_add_zeta6' + zeta6_mul_zeta6'
    rcases mul_eq_zero.mp this with h' | h'
    · left; linear_combination h'
    · right; linear_combination h'
  · rintro (rfl | rfl)
    · exact isPrimitiveRoot_zeta6
    · exact isPrimitiveRoot_zeta6'

lemma moebius_six : (ArithmeticFunction.moebius 6 : ℤ) = 1 := by
  have h : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  norm_num

/-- The sum of the primitive 6-th roots of unity in `ℂ` equals `μ(6)`. -/
theorem mobius_root_sum_6 :
    ∑ z ∈ primitiveRoots 6 ℂ, z = (ArithmeticFunction.moebius 6 : ℂ) := by
  rw [primitiveRoots_six, Finset.sum_insert (by simpa using zeta6_ne_zeta6'),
    Finset.sum_singleton, zeta6_add_zeta6']
  rw [show ((ArithmeticFunction.moebius 6 : ℤ) : ℂ) = ((1 : ℤ) : ℂ) from congrArg _ moebius_six]
  norm_num

end Math

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

