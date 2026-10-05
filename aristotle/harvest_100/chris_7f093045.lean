/-
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `k ↦ ω ^ k` on `ZMod 5`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

/-- The unnormalized discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) (a : ZMod 5) : ℂ := ∑ x : ZMod 5, f x * e (a * x)

lemma omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  push_cast
  rw [show (5 : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I by ring]
  exact Complex.exp_two_pi_mul_I

lemma omega_ne_one : omega ≠ 1 :=
  (Complex.isPrimitiveRoot_exp 5 (by norm_num)).ne_one (by norm_num)

lemma omega_pow_mod (n : ℕ) : omega ^ (n % 5) = omega ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma norm_omega : ‖omega‖ = 1 := by
  have h : ‖omega‖ ^ 5 = 1 := by
    rw [← norm_pow, omega_pow_five, norm_one]
  have hnn : (0 : ℝ) ≤ ‖omega‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖omega‖ - 1), sq_nonneg (‖omega‖ + 1), sq_nonneg ‖omega‖,
    sq_nonneg (‖omega‖ ^ 2 - 1)]

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_add (j k : ZMod 5) : e (j + k) = e j * e k := by
  simp only [e, ZMod.val_add, omega_pow_mod, pow_add]

lemma norm_e (k : ZMod 5) : ‖e k‖ = 1 := by
  simp [e, norm_pow, norm_omega]

lemma e_ne_zero (k : ZMod 5) : e k ≠ 0 := by
  intro h
  have := norm_e k
  rw [h] at this
  simp at this

lemma e_neg (k : ZMod 5) : e (-k) = (e k)⁻¹ := by
  have h : e (-k) * e k = 1 := by rw [← e_add]; simp [e_zero]
  field_simp [e_ne_zero k] at h ⊢
  linear_combination h

lemma conj_e (k : ZMod 5) : (starRingEnd ℂ) (e k) = e (-k) := by
  rw [e_neg, Complex.inv_eq_conj (norm_e k)]

lemma sum_omega_pow_range : ∑ j ∈ Finset.range 5, omega ^ j = 0 := by
  rw [geom_sum_eq omega_ne_one, omega_pow_five]
  simp

lemma sum_e_univ : ∑ a : ZMod 5, e a = 0 := by
  have h : ∑ a : ZMod 5, e a = ∑ j ∈ Finset.range 5, omega ^ j := by
    simp only [e]
    rfl
  rw [h, sum_omega_pow_range]

/-- Orthogonality of the character `e`. -/
lemma sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hk : k = 0
  · subst hk
    simp [e_zero, Finset.card_univ]
  · rw [if_neg hk]
    have := Equiv.sum_comp (Equiv.mulRight₀ k hk) e
    simpa [Equiv.mulRight₀, sum_e_univ] using this.trans sum_e_univ

/-- The complex-valued core of Parseval's identity. -/
lemma parseval_core (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
  have expand : ∀ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ x : ZMod 5, ∑ y : ZMod 5,
        (f x * (starRingEnd ℂ) (f y)) * e (a * (x - y)) := by
    intro a
    rw [dft, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, conj_e]
    have : e (a * x) * e (-(a * y)) = e (a * (x - y)) := by
      rw [← e_add]; ring_nf
    rw [← this]; ring
  calc ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ a : ZMod 5, ∑ x : ZMod 5, ∑ y : ZMod 5,
        (f x * (starRingEnd ℂ) (f y)) * e (a * (x - y)) := by
        exact Finset.sum_congr rfl fun a _ => expand a
    _ = ∑ x : ZMod 5, ∑ y : ZMod 5, (f x * (starRingEnd ℂ) (f y)) *
          ∑ a : ZMod 5, e (a * (x - y)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => by rw [Finset.mul_sum]
    _ = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
        simp only [sum_e_mul, sub_eq_zero, mul_ite, mul_zero]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_ite_eq Finset.univ x
          (fun y => f x * (starRingEnd ℂ) (f y) * 5)]
        simp [mul_comm]

theorem parseval (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, ‖dft f a‖ ^ 2 = 5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 := by
  have key : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h := parseval_core f
  simp only [key] at h
  have h2 : ((∑ a : ZMod 5, ‖dft f a‖ ^ 2 : ℝ) : ℂ)
      = ((5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast at h ⊢
    exact h
  exact_mod_cast h2

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

