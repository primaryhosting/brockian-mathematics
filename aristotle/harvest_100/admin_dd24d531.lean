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
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character on `ZMod 5`: `e x = ω ^ x`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

lemma isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

/-- The five fifth roots of unity sum to zero. -/
lemma sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 :=
  isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

lemma sum_omega_pow' : omega ^ 0 + omega ^ 1 + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  have h := sum_omega_pow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  linear_combination h

/-- Additive-character orthogonality on `ZMod 5`:
`∑ x, e (a * x)` equals `5` when `a = 0` and `0` otherwise. -/
theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  have hs := sum_omega_pow'
  have hexp : ∀ f : ZMod 5 → ℂ, ∑ x : ZMod 5, f x = f 0 + f 1 + f 2 + f 3 + f 4 := by
    intro f
    show ∑ x : Fin 5, f x = _
    rw [Fin.sum_univ_five]
  have ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by revert a; decide
  rw [hexp]
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    [rw [if_pos rfl]; rw [if_neg (by decide)]; rw [if_neg (by decide)];
      rw [if_neg (by decide)]; rw [if_neg (by decide)]] <;>
    simp only [e] <;>
    norm_num [ZMod.val_mul, ZMod.val] <;>
    linear_combination hs

end Brockian.Characters5

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

