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
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character on `ZMod 5`, `e x = ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

theorem isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 :=
  Complex.isPrimitiveRoot_exp 5 (by norm_num)

theorem omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

theorem omega_ne_one : omega ≠ 1 := fun h =>
  isPrimitiveRoot_omega.pow_ne_one_of_pos_of_lt (l := 1) (by norm_num) (by norm_num) (by simp [h])

/-- The five fifth-roots of unity sum to zero. -/
theorem sum_five_powers : (1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 : ℂ) = 0 := by
  have hz : (omega - 1) * (1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4) = 0 := by
    linear_combination omega_pow_five
  rcases mul_eq_zero.1 hz with h | h
  · exact absurd (sub_eq_zero.1 h) omega_ne_one
  · exact h

theorem sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  linear_combination sum_five_powers

theorem sum_e : ∑ x : ZMod 5, e x = 0 := by
  show ∑ x : ZMod 5, omega ^ x.val = 0
  rw [show (∑ x : ZMod 5, omega ^ x.val) = ∑ x : Fin 5, omega ^ (x : ℕ) from rfl,
    Fin.sum_univ_five]
  norm_num
  linear_combination sum_five_powers

/-- Additive-character orthogonality on `ZMod 5`:
`∑ x, e (a * x)` equals `5` when `a = 0` and `0` otherwise. -/
theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases ha : a = 0
  · subst ha
    simp [e, ZMod.val_zero]
  · rw [if_neg ha, ← sum_e]
    exact Equiv.sum_comp (Equiv.mulLeft₀ a ha) e

end Brockian.Characters5

