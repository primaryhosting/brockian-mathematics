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

local notation "ω" => Brockian.Characters5.omega

/-- The standard additive character on `ZMod 5`. -/
noncomputable def e (k : ZMod 5) : ℂ := ω ^ k.val

lemma omega_pow_five : ω ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  have : (5 : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I := by
    field_simp
  push_cast
  rw [this, Complex.exp_two_pi_mul_I]

lemma omega_ne_one : ω ≠ 1 := by
  rw [omega]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) * (1 - n * 5) = 0 := by
    ring_nf; ring_nf at hn; linear_combination 5 * hn
  rcases mul_eq_zero.1 h2 with h | h
  · simp [hpi, hI] at h
  · have h1 : (1 : ℂ) = n * 5 := sub_eq_zero.mp h
    have h1' : (1 : ℤ) = n * 5 := by exact_mod_cast h1
    omega

lemma omega_pow_mod (n : ℕ) : ω ^ (n % 5) = ω ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

@[simp] lemma e_zero : e 0 = 1 := by simp [e]

lemma e_add (a b : ZMod 5) : e (a + b) = e a * e b := by
  simp only [e, ZMod.val_add, omega_pow_mod, pow_add]

lemma sum_omega_pow : (1 : ℂ) + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have h : (ω - 1) * (1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4) = 0 := by
    have := omega_pow_five
    linear_combination this
  rcases mul_eq_zero.1 h with h1 | h2
  · exact absurd (sub_eq_zero.1 h1) omega_ne_one
  · exact h2

lemma sum_e : ∑ b : ZMod 5, e b = 0 := by
  show ∑ b : Fin 5, e b = 0
  rw [Fin.sum_univ_five]
  have h0 : e (0 : Fin 5) = 1 := by simp [e]
  have h1 : e (1 : Fin 5) = ω := by
    show ω ^ (1 : ZMod 5).val = ω
    rw [show (1 : ZMod 5).val = 1 from rfl, pow_one]
  have h2 : e (2 : Fin 5) = ω ^ 2 := by show ω ^ (2 : ZMod 5).val = ω ^ 2; rfl
  have h3 : e (3 : Fin 5) = ω ^ 3 := by show ω ^ (3 : ZMod 5).val = ω ^ 3; rfl
  have h4 : e (4 : Fin 5) = ω ^ 4 := by show ω ^ (4 : ZMod 5).val = ω ^ 4; rfl
  rw [h0, h1, h2, h3, h4]
  exact sum_omega_pow

lemma sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [if_neg hk]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have : ∑ a : ZMod 5, e (a * k) = ∑ b : ZMod 5, e b :=
      Fintype.sum_equiv (Equiv.mulRight₀ k hk) _ _ (fun a => rfl)
    rw [this, sum_e]

/-- The discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) : ZMod 5 → ℂ := fun a => ∑ x : ZMod 5, e (a * x) * f x

theorem dft_inversion (f : ZMod 5 → ℂ) (x : ZMod 5) :
    f x = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (-(a * x)) * dft f a := by
  have key : ∑ a : ZMod 5, e (-(a * x)) * dft f a
      = ∑ y : ZMod 5, f y * (if y - x = 0 then (5 : ℂ) else 0) := by
    simp only [dft, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : ∀ a : ZMod 5, e (-(a * x)) * (e (a * y) * f y) = e (a * (y - x)) * f y := by
      intro a
      rw [← mul_assoc, ← e_add]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun a _ => this a), ← Finset.sum_mul, sum_e_mul, mul_comm]
  rw [key]
  have : ∀ y : ZMod 5, f y * (if y - x = 0 then (5 : ℂ) else 0)
      = if y = x then f y * 5 else 0 := by
    intro y
    by_cases h : y = x
    · simp [h]
    · rw [if_neg h, if_neg (fun hc => h (sub_eq_zero.1 hc)), mul_zero]
  rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_ite_eq' Finset.univ x (fun y => f y * 5)]
  rw [if_pos (Finset.mem_univ x)]
  ring

end Brockian.Characters5

