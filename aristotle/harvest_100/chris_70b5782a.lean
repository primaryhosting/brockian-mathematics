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

/-- A fixed primitive 6-th root of unity in `ℂ`. -/
noncomputable def zeta6 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 6)

lemma isPrimitiveRoot_zeta6 : IsPrimitiveRoot zeta6 6 :=
  Complex.isPrimitiveRoot_exp 6 (by norm_num)

lemma zeta6_pow_three : zeta6 ^ 3 = -1 := by
  have h6 : zeta6 ^ 6 = 1 := isPrimitiveRoot_zeta6.pow_eq_one
  have hne : zeta6 ^ 3 ≠ 1 :=
    isPrimitiveRoot_zeta6.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (zeta6 ^ 3 - 1) * (zeta6 ^ 3 + 1) = 0 := by linear_combination h6
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (by linear_combination h : zeta6 ^ 3 = 1) hne
  · linear_combination h

lemma zeta6_sq_sub : zeta6 ^ 2 - zeta6 + 1 = 0 := by
  have hne : zeta6 ≠ -1 := by
    intro h
    exact isPrimitiveRoot_zeta6.pow_ne_one_of_pos_of_lt (l := 2) (by norm_num) (by norm_num)
      (by rw [h]; norm_num)
  have hfac : (zeta6 + 1) * (zeta6 ^ 2 - zeta6 + 1) = 0 := by
    linear_combination zeta6_pow_three
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (by linear_combination h : zeta6 = -1) hne
  · exact h

/-- The primitive 6-th roots of unity in `ℂ` are exactly `ζ` and `ζ⁵`. -/
lemma primitiveRoots_six : primitiveRoots 6 ℂ = {zeta6, zeta6 ^ 5} := by
  ext x
  rw [mem_primitiveRoots (by norm_num), isPrimitiveRoot_zeta6.isPrimitiveRoot_iff,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi6, hcop, rfl⟩
    interval_cases i <;> first
      | (exfalso; revert hcop; decide)
      | simp
  · rintro (rfl | rfl)
    · exact ⟨1, by norm_num⟩
    · exact ⟨5, by norm_num, by decide, rfl⟩

lemma zeta6_ne_pow_five : zeta6 ≠ zeta6 ^ 5 := by
  intro h
  have := isPrimitiveRoot_zeta6.pow_inj (i := 1) (j := 5) (by norm_num) (by norm_num)
    (by simpa using h)
  omega

theorem mobius_root_sum_6 :
    ∑ z ∈ primitiveRoots 6 ℂ, z = (ArithmeticFunction.moebius 6 : ℂ) := by
  have hmu : ArithmeticFunction.moebius 6 = 1 := by
    have h : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num)]
    simp [ArithmeticFunction.moebius_apply_prime, Nat.prime_two, Nat.prime_three]
  rw [primitiveRoots_six, Finset.sum_pair zeta6_ne_pow_five, hmu]
  push_cast
  linear_combination (zeta6 ^ 2) * zeta6_pow_three - zeta6_sq_sub

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

