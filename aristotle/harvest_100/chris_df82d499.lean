import Mathlib

/-!
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
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

open Complex

/-- The primitive fifth root of unity `exp (2πi/5)`. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e k = ω ^ k` on `ZMod 5`. -/
noncomputable def e (k : ZMod 5) : ℂ := ω ^ k.val

/-- The (unnormalized) discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) (a : ZMod 5) : ℂ := ∑ x : ZMod 5, f x * e (a * x)

lemma omega_pow_five : ω ^ 5 = 1 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [ω] using h.pow_eq_one

lemma omega_ne_one : ω ≠ 1 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [ω] using h.ne_one (by norm_num)

lemma omega_pow_mod (n : ℕ) : ω ^ (n % 5) = ω ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma norm_omega : ‖ω‖ = 1 := by
  simp [ω, Complex.norm_exp]

lemma norm_e (k : ZMod 5) : ‖e k‖ = 1 := by
  simp [e, norm_pow, norm_omega]

lemma e_ne_zero (k : ZMod 5) : e k ≠ 0 := by
  intro h
  have hk := norm_e k
  rw [h] at hk
  simp at hk

lemma e_zero : e 0 = 1 := by
  simp [e]

lemma e_add (j k : ZMod 5) : e (j + k) = e j * e k := by
  simp only [e, ZMod.val_add, ← pow_add]
  exact omega_pow_mod _

lemma e_neg (k : ZMod 5) : e (-k) = (e k)⁻¹ := by
  have h : e (-k) * e k = 1 := by
    rw [← e_add]
    simp [e_zero]
  field_simp [e_ne_zero k] at h ⊢
  linear_combination h

lemma conj_e (k : ZMod 5) : (starRingEnd ℂ) (e k) = e (-k) := by
  rw [e_neg, Complex.inv_eq_conj (norm_e k)]

lemma e_mul_conj_e (a x y : ZMod 5) :
    e (a * x) * (starRingEnd ℂ) (e (a * y)) = e (a * (x - y)) := by
  rw [conj_e, ← e_add, mul_sub, sub_eq_add_neg]

lemma sum_univ_zmod_five (g : ZMod 5 → ℂ) :
    ∑ x : ZMod 5, g x = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have h : ∑ x : ZMod 5, g x = ∑ x : Fin 5, g x := rfl
  rw [h, Fin.sum_univ_five]

lemma geom_sum_omega : 1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have hne : ω - 1 ≠ 0 := sub_ne_zero.mpr omega_ne_one
  have h : (ω - 1) * (1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4) = 0 := by
    linear_combination omega_pow_five
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h hne
  · exact h

lemma sum_e : ∑ a : ZMod 5, e a = 0 := by
  rw [sum_univ_zmod_five]
  show ω ^ (0 : ZMod 5).val + ω ^ (1 : ZMod 5).val + ω ^ (2 : ZMod 5).val + ω ^ (3 : ZMod 5).val
      + ω ^ (4 : ZMod 5).val = 0
  rw [show (0 : ZMod 5).val = 0 from rfl, show (1 : ZMod 5).val = 1 from rfl,
    show (2 : ZMod 5).val = 2 from rfl, show (3 : ZMod 5).val = 3 from rfl,
    show (4 : ZMod 5).val = 4 from rfl]
  linear_combination geom_sum_omega

/-- Orthogonality of the characters of `ZMod 5`. -/
lemma sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hk : k = 0
  · subst hk
    simp [e]
  · rw [if_neg hk, ← sum_e]
    exact Equiv.sum_comp (Equiv.mulRight₀ k hk) e

/-- The complex-valued form of Parseval's identity. -/
lemma parseval_core (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
  have hexp : ∀ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ x : ZMod 5, ∑ y : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (x - y)) := by
    intro a
    rw [dft, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, ← e_mul_conj_e a x y]
    ring
  calc ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ a : ZMod 5, ∑ x : ZMod 5, ∑ y : ZMod 5,
          f x * (starRingEnd ℂ) (f y) * e (a * (x - y)) :=
        Finset.sum_congr rfl fun a _ => hexp a
    _ = ∑ x : ZMod 5, ∑ y : ZMod 5, ∑ a : ZMod 5,
          f x * (starRingEnd ℂ) (f y) * e (a * (x - y)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x : ZMod 5, ∑ y : ZMod 5,
          f x * (starRingEnd ℂ) (f y) * (if y = x then (5 : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.mul_sum, sum_e_mul (x - y)]
        have h : (x - y = 0) = (y = x) := by simp [sub_eq_zero, eq_comm]
        simp only [h]
    _ = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [mul_ite, Finset.sum_ite_eq']
        ring

/-- Parseval/Plancherel on `ZMod 5` for the unnormalized discrete Fourier transform. -/
theorem parseval (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, ‖dft f a‖ ^ 2 = 5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 := by
  have h := parseval_core f
  simp only [Complex.mul_conj'] at h
  have h2 : ((∑ a : ZMod 5, ‖dft f a‖ ^ 2 : ℝ) : ℂ)
      = ((5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact h
  exact_mod_cast h2

end Brockian.Characters5

