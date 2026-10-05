/-
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

/-- The (unnormalized) discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) (a : ZMod 5) : ℂ := ∑ x : ZMod 5, f x * e (a * x)

lemma omega_ne_zero : omega ≠ 0 := Complex.exp_ne_zero _

lemma omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  rw [show ((5 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 5) = (2 * Real.pi) * Complex.I by
    push_cast; ring]
  simp

lemma omega_ne_one : omega ≠ 1 := by
  intro h
  have h2 : Complex.exp (2 * Real.pi * Complex.I / 5) = 1 := by rw [← omega]; exact h
  rw [Complex.exp_eq_one_iff] at h2
  obtain ⟨n, hn⟩ := h2
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp at hn
  have hn5 : (1 : ℤ) = 5 * n := by exact_mod_cast hn
  omega

lemma omega_pow_mod (n : ℕ) : omega ^ (n % 5) = omega ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_add (a b : ZMod 5) : e (a + b) = e a * e b := by
  simp only [e, ZMod.val_add, omega_pow_mod, pow_add]

lemma e_ne_zero (k : ZMod 5) : e k ≠ 0 := pow_ne_zero _ omega_ne_zero

lemma norm_e (k : ZMod 5) : ‖e k‖ = 1 := by
  have : ‖omega‖ = 1 := by
    rw [omega, Complex.norm_exp]
    norm_num
  simp [e, norm_pow, this]

lemma conj_e (k : ZMod 5) : (starRingEnd ℂ) (e k) = e (-k) := by
  have h1 : e k * e (-k) = 1 := by rw [← e_add, add_neg_cancel, e_zero]
  have h2 : e k * (starRingEnd ℂ) (e k) = 1 := by
    rw [Complex.mul_conj', norm_e]
    norm_num
  have := h1.trans h2.symm
  exact (mul_left_cancel₀ (e_ne_zero k) this).symm

lemma sum_e_univ : ∑ b : ZMod 5, e b = 0 := by
  have hgeom : (omega - 1) * (1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4)
      = omega ^ 5 - 1 := by ring
  rw [omega_pow_five, sub_self] at hgeom
  have hne : omega - 1 ≠ 0 := sub_ne_zero.mpr omega_ne_one
  have hsum : (1 : ℂ) + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
    rcases mul_eq_zero.mp hgeom with h | h
    · exact absurd h hne
    · exact h
  have : ∑ b : ZMod 5, e b = 1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 := by
    show ∑ b : Fin 5, e b = _
    rw [Fin.sum_univ_five]
    simp [e, ZMod.val]
  rw [this, hsum]

/-- Orthogonality of the character sums. -/
lemma sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [e_zero]
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [if_neg hk]
    rw [← sum_e_univ]
    exact Fintype.sum_equiv (Equiv.mulRight₀ k hk) _ _ (fun a => rfl)

/-- The complex-valued core of Parseval's identity. -/
theorem parseval_core (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
  have expand : ∀ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ x : ZMod 5, ∑ y : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (x - y)) := by
    intro a
    rw [dft, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [map_mul, conj_e]
    have harg : a * x + -(a * y) = a * (x - y) := by ring
    rw [show f x * e (a * x) * ((starRingEnd ℂ) (f y) * e (-(a * y)))
        = f x * (starRingEnd ℂ) (f y) * (e (a * x) * e (-(a * y))) by ring,
      ← e_add, harg]
  simp only [expand]
  rw [Finset.sum_comm]
  have step : ∀ x : ZMod 5, ∑ a : ZMod 5, ∑ y : ZMod 5,
      f x * (starRingEnd ℂ) (f y) * e (a * (x - y))
      = 5 * (f x * (starRingEnd ℂ) (f x)) := by
    intro x
    rw [Finset.sum_comm]
    have : ∀ y : ZMod 5, ∑ a : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (x - y))
        = if y = x then 5 * (f x * (starRingEnd ℂ) (f y)) else 0 := by
      intro y
      rw [← Finset.mul_sum, sum_e_mul]
      by_cases hxy : x - y = 0
      · have : y = x := by
          have := sub_eq_zero.mp hxy
          exact this.symm
        simp [this, mul_comm]
      · have hne : y ≠ x := fun h => hxy (by rw [h]; ring)
        simp [hxy, hne]
    rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_ite_eq' Finset.univ x]
    simp
  rw [Finset.sum_congr rfl (fun x _ => step x), ← Finset.mul_sum]

/-- Parseval/Plancherel identity on `ZMod 5` for the unnormalized transform. -/
theorem parseval (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, ‖dft f a‖ ^ 2 = 5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 := by
  have hc : ((∑ a : ZMod 5, ‖dft f a‖ ^ 2 : ℝ) : ℂ)
      = ((5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    simp only [← Complex.mul_conj']
    exact parseval_core f
  exact_mod_cast hc

end Characters5
end Brockian

