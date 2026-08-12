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
noncomputable def zeta6 : ℂ := (1 + Complex.I * Real.sqrt 3) / 2

/-- The other primitive 6-th root of unity, `exp (-π i / 3) = (1 - i √3) / 2`. -/
noncomputable def zeta6' : ℂ := (1 - Complex.I * Real.sqrt 3) / 2

private lemma sqrt_three_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  norm_cast
  rw [Real.sq_sqrt]
  norm_num

/-- Any complex number satisfying `z ^ 2 = z - 1` (i.e. a root of the 6-th cyclotomic
polynomial `X ^ 2 - X + 1`) is a primitive 6-th root of unity. -/
lemma isPrimitiveRoot_six_of_sq_eq {z : ℂ} (hz : z ^ 2 = z - 1) : IsPrimitiveRoot z 6 := by
  have h3 : z ^ 3 = -1 := by linear_combination (z + 1) * hz
  have h4 : z ^ 4 = -z := by linear_combination z * h3
  have h5 : z ^ 5 = 1 - z := by linear_combination z ^ 2 * h3 - hz
  have h6 : z ^ 6 = 1 := by linear_combination (z ^ 3 - 1) * h3
  refine IsPrimitiveRoot.mk_of_lt z (by norm_num) h6 ?_
  intro l hl hl6
  interval_cases l
  · intro h
    rw [pow_one] at h
    rw [h] at hz
    norm_num at hz
  · intro h
    rw [hz] at h
    have hz2 : z = 2 := by linear_combination h
    rw [hz2] at hz
    norm_num at hz
  · rw [h3]
    norm_num
  · intro h
    rw [h4] at h
    have hz2 : z = -1 := by linear_combination -h
    rw [hz2] at hz
    norm_num at hz
  · intro h
    rw [h5] at h
    have hz2 : z = 0 := by linear_combination -h
    rw [hz2] at hz
    norm_num at hz

lemma isPrimitiveRoot_zeta6 : IsPrimitiveRoot zeta6 6 := by
  refine isPrimitiveRoot_six_of_sq_eq ?_
  simp only [zeta6]
  linear_combination (-1 / 4 : ℂ) * sqrt_three_sq +
    (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq

lemma isPrimitiveRoot_zeta6' : IsPrimitiveRoot zeta6' 6 := by
  refine isPrimitiveRoot_six_of_sq_eq ?_
  simp only [zeta6']
  linear_combination (-1 / 4 : ℂ) * sqrt_three_sq +
    (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq

lemma zeta6_ne_zeta6' : zeta6 ≠ zeta6' := by
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  intro h
  have him : zeta6.im = zeta6'.im := by rw [h]
  simp only [zeta6, zeta6'] at him
  simp at him
  linarith

/-- The primitive 6-th roots of unity in `ℂ` are exactly `(1 ± i √3) / 2`. -/
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
theorem mobius_root_sum_6 :
    ∑ z ∈ primitiveRoots 6 ℂ, z = ((ArithmeticFunction.moebius 6 : ℤ) : ℂ) := by
  have hmu : ArithmeticFunction.moebius 6 = 1 := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree (by decide +kernel)]
    simp [ArithmeticFunction.cardFactors]
  rw [primitiveRoots_six_complex, Finset.sum_pair zeta6_ne_zeta6', hmu]
  simp only [zeta6, zeta6']
  push_cast
  ring

end Math

