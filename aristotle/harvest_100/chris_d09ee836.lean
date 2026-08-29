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

import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Classical

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character `e` on `ZMod 5`, given by `x ↦ ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

theorem isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega] using h

theorem omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

/-- The sum of all fifth powers of `ω` vanishes. -/
theorem sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 :=
  isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

theorem sum_omega_pow' : 1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  have h := sum_omega_pow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h
  linear_combination h

/-- Expanding a sum over `ZMod 5`. -/
theorem sum_zmod5 (f : ZMod 5 → ℂ) : ∑ x : ZMod 5, f x = f 0 + f 1 + f 2 + f 3 + f 4 := by
  show ∑ x : Fin 5, f x = _
  rw [Fin.sum_univ_five]

/-- The full character sum vanishes. -/
theorem sum_e : ∑ x : ZMod 5, e x = 0 := by
  rw [sum_zmod5]
  show omega ^ (0 : ℕ) + omega ^ (1 : ℕ) + omega ^ (2 : ℕ) + omega ^ (3 : ℕ) + omega ^ (4 : ℕ) = 0
  linear_combination sum_omega_pow'

/-- Additive-character orthogonality on `ZMod 5`. -/
theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp only [zero_mul, e]
    show ∑ _x : ZMod 5, omega ^ (0 : ℕ) = 5
    simp
  · rw [if_neg ha]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    calc ∑ x : ZMod 5, e (a * x) = ∑ x : ZMod 5, e x :=
          Fintype.sum_bijective (fun x => a * x) (mulLeft_bijective₀ a ha) _ _ (fun _ => rfl)
      _ = 0 := sum_e

end Characters5
end Brockian

