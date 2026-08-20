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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character on `ZMod 5` with values in `ℂ`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

theorem isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

/-- The geometric sum of the fifth roots of unity vanishes. -/
theorem sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 :=
  isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

theorem omega_geom : 1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  have h := sum_omega_pow
  simp [Finset.sum_range_succ] at h
  linear_combination h

/-- Expansion of a sum over `ZMod 5` into its five terms. -/
theorem sum_zmod_five (f : ZMod 5 → ℂ) :
    ∑ x : ZMod 5, f x = f 0 + f 1 + f 2 + f 3 + f 4 := by
  show ∑ x : Fin 5, f x = _
  rw [Fin.sum_univ_five]

/-- Additive-character orthogonality on `ZMod 5`:
`∑ x, e (a * x)` is `5` when `a = 0` and `0` otherwise. -/
theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  have hg := omega_geom
  have h : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by revert a; decide
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rw [sum_zmod_five] <;>
    norm_num [e, ZMod.val, Fin.mul_def, show ((1 : ZMod 5) ≠ 0) by decide,
      show ((2 : ZMod 5) ≠ 0) by decide, show ((3 : ZMod 5) ≠ 0) by decide,
      show ((4 : ZMod 5) ≠ 0) by decide] <;>
    linear_combination hg

end Characters5
end Brockian

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

