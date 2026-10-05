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
noncomputable def omg : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e` of `ZMod 5` given by `e k = ω ^ k`. -/
noncomputable def e (k : ZMod 5) : ℂ := omg ^ k.val

lemma omega_pow_five : omg ^ 5 = 1 := by
  rw [omg, ← Complex.exp_nat_mul]
  rw [show ((5 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I by
    push_cast; ring]
  simp [Complex.exp_two_pi_mul_I]

lemma omega_ne_one : omg ≠ 1 := by
  intro h
  rw [omg, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI := Complex.I_ne_zero
  field_simp at hn
  have h5 : (5 : ℤ) ∣ 1 := ⟨n, by exact_mod_cast hn⟩
  omega

lemma omega_pow_mod (n : ℕ) : omg ^ (n % 5) = omg ^ n := by
  conv_rhs => rw [show n = 5 * (n / 5) + n % 5 by omega]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma e_add (a b : ZMod 5) : e (a + b) = e a * e b := by
  simp only [e, ZMod.val_add, omega_pow_mod, pow_add]

lemma e_zero : e 0 = 1 := by simp [e]

lemma sum_zmod5 (g : ZMod 5 → ℂ) : ∑ x : ZMod 5, g x = g 0 + g 1 + g 2 + g 3 + g 4 := by
  show ∑ x : Fin 5, g x = _
  rw [Fin.sum_univ_five]

lemma sum_omega : 1 + omg + omg ^ 2 + omg ^ 3 + omg ^ 4 = 0 := by
  have key : (omg - 1) * (1 + omg + omg ^ 2 + omg ^ 3 + omg ^ 4) = omg ^ 5 - 1 := by ring
  rw [omega_pow_five, sub_self] at key
  rcases mul_eq_zero.mp key with h | h
  · exact absurd (sub_eq_zero.mp h) omega_ne_one
  · exact h

lemma sum_e_all : ∑ a : ZMod 5, e a = 0 := by
  rw [sum_zmod5]
  simp only [e, show ZMod.val (0 : ZMod 5) = 0 from rfl, show ZMod.val (1 : ZMod 5) = 1 from rfl,
    show ZMod.val (2 : ZMod 5) = 2 from rfl, show ZMod.val (3 : ZMod 5) = 3 from rfl,
    show ZMod.val (4 : ZMod 5) = 4 from rfl, pow_zero, pow_one]
  linear_combination sum_omega

/-- Orthogonality of the characters on `ZMod 5`. -/
lemma sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [e]
  · rw [if_neg hk]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    calc ∑ a : ZMod 5, e (a * k) = ∑ a : ZMod 5, e ((Equiv.mulRight₀ k hk) a) := rfl
      _ = ∑ b : ZMod 5, e b := Equiv.sum_comp _ _
      _ = 0 := sum_e_all

/-- The discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) : ZMod 5 → ℂ := fun a => ∑ x : ZMod 5, e (a * x) * f x

/-- Fourier inversion on `ZMod 5`. -/
theorem dft_inversion (f : ZMod 5 → ℂ) (x : ZMod 5) :
    f x = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (-(a * x)) * dft f a := by
  have key : ∀ a y : ZMod 5, e (-(a * x)) * (e (a * y) * f y) = e (a * (y - x)) * f y := by
    intro a y
    rw [← mul_assoc, ← e_add]
    congr 2
    ring
  have h1 : ∑ a : ZMod 5, e (-(a * x)) * dft f a
      = ∑ y : ZMod 5, (if y - x = 0 then (5 : ℂ) else 0) * f y := by
    have hexp : ∀ a : ZMod 5, e (-(a * x)) * dft f a = ∑ y : ZMod 5, e (a * (y - x)) * f y := by
      intro a
      rw [dft, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => key a y
    rw [Finset.sum_congr rfl fun a _ => hexp a, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, sum_e_mul]
  rw [h1]
  have h2 : ∀ y : ZMod 5, (if y - x = 0 then (5 : ℂ) else 0) * f y
      = if y = x then (5 : ℂ) * f x else 0 := by
    intro y
    by_cases h : y = x
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc => h (sub_eq_zero.mp hc)), zero_mul]
  rw [Finset.sum_congr rfl fun y _ => h2 y, Finset.sum_ite_eq' Finset.univ x]
  simp

end Brockian.Characters5

