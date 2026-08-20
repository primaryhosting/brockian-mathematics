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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e : ZMod 5 → ℂ`, `e k = ω ^ k`. -/
noncomputable def e (k : ZMod 5) : ℂ := ω ^ k.val

/-- The discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) : ZMod 5 → ℂ := fun a => ∑ x : ZMod 5, e (a * x) * f x

theorem omega_pow_five : ω ^ 5 = 1 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [ω] using h.pow_eq_one

theorem omega_pow_mod (n : ℕ) : ω ^ (n % 5) = ω ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

theorem e_add (u v : ZMod 5) : e (u + v) = e u * e v := by
  simp [e, ZMod.val_add, omega_pow_mod, pow_add]

theorem e_zero : e 0 = 1 := by simp [e]

theorem e_neg_mul_self (k : ZMod 5) : e (-k) * e k = 1 := by
  rw [← e_add]; simp [e_zero]

/-- Expansion of a sum over `ZMod 5`. -/
theorem sum_five (g : ZMod 5 → ℂ) : ∑ b : ZMod 5, g b = g 0 + g 1 + g 2 + g 3 + g 4 := by
  show ∑ b : Fin 5, g b = _
  rw [Fin.sum_univ_five]

theorem omega_geom_sum : 1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have hp := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  have h := hp.geom_sum_eq_zero (by norm_num)
  simp [Finset.sum_range_succ] at h
  simpa [ω] using h

theorem sum_e : ∑ b : ZMod 5, e b = 0 := by
  rw [sum_five]
  show ω ^ (0 : ZMod 5).val + ω ^ (1 : ZMod 5).val + ω ^ (2 : ZMod 5).val + ω ^ (3 : ZMod 5).val
      + ω ^ (4 : ZMod 5).val = 0
  norm_num [show (0 : ZMod 5).val = 0 from rfl, show (1 : ZMod 5).val = 1 from rfl,
    show (2 : ZMod 5).val = 2 from rfl, show (3 : ZMod 5).val = 3 from rfl,
    show (4 : ZMod 5).val = 4 from rfl]
  linear_combination omega_geom_sum

/-- Orthogonality of the characters. -/
theorem sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hk : k = 0
  · subst hk; simp [e]
  · rw [if_neg hk, ← sum_e]
    exact Equiv.sum_comp (Equiv.mulRight₀ k hk) e

/-- Fourier inversion on `ZMod 5`. -/
theorem dft_inversion (f : ZMod 5 → ℂ) (x : ZMod 5) :
    f x = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (-(a * x)) * dft f a := by
  have key : ∀ a : ZMod 5, e (-(a * x)) * dft f a = ∑ y : ZMod 5, e (a * (y - x)) * f y := by
    intro a
    rw [dft, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← mul_assoc, ← e_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl fun a _ => key a, Finset.sum_comm]
  have hy : ∀ y : ZMod 5, ∑ a : ZMod 5, e (a * (y - x)) * f y
      = (if y = x then (5 : ℂ) else 0) * f y := by
    intro y
    rw [← Finset.sum_mul, sum_e_mul]
    simp [sub_eq_zero]
  rw [Finset.sum_congr rfl fun y _ => hy y]
  simp [ite_mul, Finset.sum_ite_eq']

end Brockian.Characters5

