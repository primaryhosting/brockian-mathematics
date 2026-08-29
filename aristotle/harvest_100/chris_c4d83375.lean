/-
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` attached to `omega`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

lemma omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul,
    show (5 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 5) = 2 * Real.pi * Complex.I by
      push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma omega_ne_one : omega ≠ 1 := by
  rw [omega, Ne, Complex.exp_eq_one_iff]
  push_neg
  intro n hn
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp at hn
  have h : (1 : ℤ) = 5 * n := by exact_mod_cast hn
  omega

lemma omega_pow_mod (n : ℕ) : omega ^ (n % 5) = omega ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma e_add (a b : ZMod 5) : e (a + b) = e a * e b := by
  simp only [e, ZMod.val_add, omega_pow_mod, pow_add]

lemma sum_zmod5 (g : ZMod 5 → ℂ) :
    ∑ i : ZMod 5, g i = g 0 + g 1 + g 2 + g 3 + g 4 :=
  Fin.sum_univ_five g

lemma geom_omega : 1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  have h : (omega - 1) * (1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4) = 0 := by
    have := omega_pow_five
    linear_combination this
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) omega_ne_one
  · exact h2

lemma sum_e : ∑ b : ZMod 5, e b = 0 := by
  rw [sum_zmod5]
  simp only [e, show ZMod.val (0 : ZMod 5) = 0 from rfl, show ZMod.val (1 : ZMod 5) = 1 from rfl,
    show ZMod.val (2 : ZMod 5) = 2 from rfl, show ZMod.val (3 : ZMod 5) = 3 from rfl,
    show ZMod.val (4 : ZMod 5) = 4 from rfl]
  linear_combination geom_omega

lemma e_zero : e 0 = 1 := by
  simp [e, show ZMod.val (0 : ZMod 5) = 0 from rfl]

lemma sum_e_mul (k : ZMod 5) :
    ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [e_zero]
  · rw [if_neg hk]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have : ∑ a : ZMod 5, e (a * k) = ∑ b : ZMod 5, e b :=
      Fintype.sum_equiv (Equiv.mulRight₀ k hk) _ _ (fun a => rfl)
    rw [this, sum_e]

/-- The discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) : ZMod 5 → ℂ := fun a => ∑ x : ZMod 5, e (a * x) * f x

theorem dft_inversion (f : ZMod 5 → ℂ) (x : ZMod 5) :
    f x = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (-(a * x)) * dft f a := by
  have key : ∑ a : ZMod 5, e (-(a * x)) * dft f a = 5 * f x := by
    have h1 : ∀ a : ZMod 5, e (-(a * x)) * dft f a
        = ∑ y : ZMod 5, e (a * (y - x)) * f y := by
      intro a
      rw [dft, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [← mul_assoc, ← e_add]
      congr 2
      ring
    calc ∑ a : ZMod 5, e (-(a * x)) * dft f a
        = ∑ a : ZMod 5, ∑ y : ZMod 5, e (a * (y - x)) * f y :=
          Finset.sum_congr rfl (fun a _ => h1 a)
      _ = ∑ y : ZMod 5, ∑ a : ZMod 5, e (a * (y - x)) * f y := Finset.sum_comm
      _ = ∑ y : ZMod 5, (if y - x = 0 then (5 : ℂ) else 0) * f y := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [← Finset.sum_mul, sum_e_mul]
      _ = ∑ y : ZMod 5, (if y = x then (5 : ℂ) else 0) * f y := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          simp [sub_eq_zero]
      _ = 5 * f x := by simp
  rw [key]
  ring

end Brockian.Characters5

