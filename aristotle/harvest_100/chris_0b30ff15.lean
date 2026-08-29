/-
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
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

set_option grind.warning false

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `k ↦ ω ^ k` on `ZMod 5`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

lemma omega_isPrimitiveRoot : IsPrimitiveRoot omega 5 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

lemma omega_pow_five : omega ^ 5 = 1 := omega_isPrimitiveRoot.pow_eq_one

lemma omega_geom_sum : 1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  simpa [Finset.sum_range_succ] using omega_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)

lemma omega_pow_mod (n : ℕ) : omega ^ (n % 5) = omega ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma e_add (a b : ZMod 5) : e (a + b) = e a * e b := by
  simp only [e, ZMod.val_add, omega_pow_mod, pow_add]

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_neg_mul_self (k : ZMod 5) : e (-k) * e k = 1 := by
  rw [← e_add, neg_add_cancel, e_zero]

lemma sum_univ_five (g : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, g a = g 0 + g 1 + g 2 + g 3 + g 4 :=
  Fin.sum_univ_five g

lemma cases_five : ∀ k : ZMod 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide

/-- Orthogonality of the characters `e`. -/
lemma sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  rw [sum_univ_five]
  rcases cases_five k with h | h | h | h | h <;> subst h <;>
    norm_num [e, show (1 : ZMod 5).val = 1 from rfl, show (2 : ZMod 5).val = 2 from rfl,
      show (3 : ZMod 5).val = 3 from rfl, show (4 : ZMod 5).val = 4 from rfl,
      show (6 : ZMod 5).val = 1 from rfl, show (8 : ZMod 5).val = 3 from rfl,
      show (9 : ZMod 5).val = 4 from rfl, show (12 : ZMod 5).val = 2 from rfl,
      show (16 : ZMod 5).val = 1 from rfl,
      show ((1 : ZMod 5) ≠ 0) from by decide, show ((2 : ZMod 5) ≠ 0) from by decide,
      show ((3 : ZMod 5) ≠ 0) from by decide, show ((4 : ZMod 5) ≠ 0) from by decide] <;>
    linear_combination omega_geom_sum

/-- The discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) : ZMod 5 → ℂ := fun a => ∑ x : ZMod 5, e (a * x) * f x

/-- Fourier inversion on `ZMod 5`. -/
theorem dft_inversion (f : ZMod 5 → ℂ) (x : ZMod 5) :
    f x = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (-(a * x)) * dft f a := by
  have key : ∀ a : ZMod 5,
      e (-(a * x)) * dft f a = ∑ y : ZMod 5, e (a * (y - x)) * f y := by
    intro a
    rw [dft, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← mul_assoc, ← e_add]
    congr 2
    ring
  have inner : ∀ y : ZMod 5,
      ∑ a : ZMod 5, e (a * (y - x)) * f y = (if y = x then (5 : ℂ) else 0) * f y := by
    intro y
    rw [← Finset.sum_mul, sum_e_mul]
    simp [sub_eq_zero]
  rw [Finset.sum_congr rfl fun a _ => key a, Finset.sum_comm,
    Finset.sum_congr rfl fun y _ => inner y]
  simp [ite_mul, Finset.sum_ite_eq']

end Brockian.Characters5

