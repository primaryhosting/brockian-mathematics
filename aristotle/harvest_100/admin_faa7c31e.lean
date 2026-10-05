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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian.Characters5

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5` with values in `ℂ`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

lemma omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  have : (5 : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I := by
    field_simp
  push_cast
  rw [this]
  exact Complex.exp_two_pi_mul_I

lemma omega_pow_mod (n : ℕ) : omega ^ (n % 5) = omega ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma e_zero : e 0 = 1 := by
  simp [e]

lemma e_add (a b : ZMod 5) : e (a + b) = e a * e b := by
  rw [e, e, e, ZMod.val_add, omega_pow_mod, pow_add]

lemma omega_ne_one : omega ≠ 1 := by
  rw [omega, Ne, Complex.exp_eq_one_iff]
  rintro ⟨n, hn⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI := Complex.I_ne_zero
  field_simp at hn
  have hn5 : (1 : ℤ) = 5 * n := by exact_mod_cast hn
  omega

/-- The full character sum vanishes: `1 + ω + ω² + ω³ + ω⁴ = 0`. -/
lemma sum_e : ∑ b : ZMod 5, e b = 0 := by
  have hfac : (omega - 1) * (∑ b : ZMod 5, e b) = omega ^ 5 - 1 := by
    simp only [e]
    show (omega - 1) * (∑ b : Fin 5, omega ^ (b : ℕ)) = omega ^ 5 - 1
    rw [Fin.sum_univ_five]
    norm_num
    ring
  rw [omega_pow_five, sub_self] at hfac
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (sub_eq_zero.1 h) omega_ne_one
  · exact h

lemma sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [e_zero, ZMod.card]
  · rw [if_neg hk]
    have : ∑ a : ZMod 5, e (a * k) = ∑ b : ZMod 5, e b :=
      Equiv.sum_comp (Equiv.mulRight₀ k hk) e
    rw [this, sum_e]

/-- The discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) : ZMod 5 → ℂ := fun a => ∑ x : ZMod 5, e (a * x) * f x

/-- Fourier inversion on `ZMod 5`. -/
theorem dft_inversion (f : ZMod 5 → ℂ) (x : ZMod 5) :
    f x = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (-(a * x)) * dft f a := by
  have key : ∑ a : ZMod 5, e (-(a * x)) * dft f a = 5 * f x := by
    simp only [dft, Finset.mul_sum]
    rw [Finset.sum_comm]
    have step : ∀ y : ZMod 5, ∑ a : ZMod 5, e (-(a * x)) * (e (a * y) * f y)
        = f y * (if y - x = 0 then (5 : ℂ) else 0) := by
      intro y
      have : ∀ a : ZMod 5, e (-(a * x)) * (e (a * y) * f y) = f y * e (a * (y - x)) := by
        intro a
        rw [← mul_assoc, ← e_add]
        rw [show -(a * x) + a * y = a * (y - x) by ring]
        ring
      simp only [this]
      rw [← Finset.mul_sum, sum_e_mul]
    have collapse : ∀ y : ZMod 5,
        f y * (if y - x = 0 then (5 : ℂ) else 0) = if y = x then 5 * f y else 0 := by
      intro y
      by_cases h : y = x
      · simp [h]; ring
      · simp [h, sub_eq_zero]
    simp only [step, collapse]
    simp
  rw [key]
  ring

end Brockian.Characters5

