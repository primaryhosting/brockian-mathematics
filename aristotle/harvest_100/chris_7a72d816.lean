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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `x ↦ ω ^ x` on `ZMod 5`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

lemma isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  have := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega] using this

lemma omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

lemma omega_ne_one : omega ≠ 1 := by
  intro h
  have := isPrimitiveRoot_omega.eq_orderOf
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

lemma omega_pow_congr {m n : ℕ} (h : m % 5 = n % 5) : omega ^ m = omega ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m 5]
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_add, pow_mul, pow_mul, omega_pow_five, one_pow, one_pow, h]

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_add (a b : ZMod 5) : e (a + b) = e a * e b := by
  rw [e, e, e, ← pow_add]
  refine omega_pow_congr ?_
  rw [ZMod.val_add]
  simp [Nat.mod_mod_of_dvd]

lemma e_neg_mul_self (k : ZMod 5) : e (-k) * e k = 1 := by
  rw [← e_add]
  simp [e_zero]

lemma sum_omega_pow : omega ^ 0 + omega ^ 1 + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  have h : (omega - 1) * (omega ^ 0 + omega ^ 1 + omega ^ 2 + omega ^ 3 + omega ^ 4) = 0 := by
    have := omega_pow_five
    ring_nf
    linear_combination this
  rcases mul_eq_zero.1 h with h1 | h2
  · exact absurd (sub_eq_zero.1 h1) omega_ne_one
  · exact h2

lemma sum_zmod5 (g : ZMod 5 → ℂ) : ∑ a : ZMod 5, g a = g 0 + g 1 + g 2 + g 3 + g 4 := by
  show ∑ a : Fin 5, g a = _
  rw [Fin.sum_univ_five]

lemma sum_e : ∑ a : ZMod 5, e a = 0 := by
  rw [sum_zmod5]
  norm_num [e, ZMod.val]
  linear_combination sum_omega_pow

/-- Orthogonality of the characters. -/
lemma sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hk : k = 0
  · subst hk
    simp [e, ZMod.val]
  · rw [if_neg hk, ← sum_e]
    exact Fintype.sum_equiv (Equiv.mulRight₀ k hk) _ _ (fun _ => rfl)

/-- The discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) : ZMod 5 → ℂ := fun a => ∑ x : ZMod 5, e (a * x) * f x

theorem dft_inversion (f : ZMod 5 → ℂ) (x : ZMod 5) :
    f x = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (-(a * x)) * dft f a := by
  have key : ∑ a : ZMod 5, e (-(a * x)) * dft f a = 5 * f x := by
    calc ∑ a : ZMod 5, e (-(a * x)) * dft f a
        = ∑ a : ZMod 5, ∑ y : ZMod 5, e (a * (y - x)) * f y := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [dft, Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← mul_assoc, ← e_add]
          ring_nf
      _ = ∑ y : ZMod 5, (∑ a : ZMod 5, e (a * (y - x))) * f y := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun y _ => by rw [Finset.sum_mul]
      _ = ∑ y : ZMod 5, (if y - x = 0 then (5 : ℂ) else 0) * f y := by
          exact Finset.sum_congr rfl fun y _ => by rw [sum_e_mul]
      _ = 5 * f x := by
          have : ∀ y : ZMod 5, (if y - x = 0 then (5 : ℂ) else 0) * f y
              = if y = x then 5 * f x else 0 := by
            intro y
            by_cases h : y = x
            · simp [h]
            · simp [sub_eq_zero, h]
          rw [Finset.sum_congr rfl fun y _ => this y, Finset.sum_ite_eq' Finset.univ x]
          simp
  rw [key]
  ring

end Characters5
end Brockian

