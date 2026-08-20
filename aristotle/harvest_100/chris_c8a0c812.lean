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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `exp (2πi/5)`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e k = ω ^ k` on `ZMod 5`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

/-- The (unnormalized) discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) (a : ZMod 5) : ℂ := ∑ x : ZMod 5, f x * e (a * x)

lemma omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul,
    show ((5 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I by
      push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma omega_ne_one : omega ≠ 1 := by
  intro h
  rw [omega, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp at hn
  have hn5 : (1 : ℤ) = 5 * n := by exact_mod_cast hn
  omega

lemma geom_sum_omega : 1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  have h : (omega - 1) * (1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4) = 0 := by
    linear_combination omega_pow_five
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd (sub_eq_zero.mp h') omega_ne_one
  · exact h'

/-- `ω ^ n` only depends on `n` mod 5. -/
lemma e_natCast (n : ℕ) : e (n : ZMod 5) = omega ^ n := by
  rw [e, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma e_add (k l : ZMod 5) : e (k + l) = e k * e l := by
  have h : ((k.val + l.val : ℕ) : ZMod 5) = k + l := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rfl
  calc e (k + l) = e ((k.val + l.val : ℕ) : ZMod 5) := by rw [h]
    _ = omega ^ (k.val + l.val) := e_natCast _
    _ = e k * e l := by rw [pow_add]; rfl

@[simp] lemma e_zero : e 0 = 1 := by simp [e]

lemma norm_e (k : ZMod 5) : ‖e k‖ = 1 := by
  rw [e, norm_pow, omega, Complex.norm_exp]
  simp

lemma conj_e (k : ZMod 5) : (starRingEnd ℂ) (e k) = e (-k) := by
  have h : e k * e (-k) = 1 := by rw [← e_add]; simp
  have hne : e k ≠ 0 := by
    intro h0
    have := norm_e k
    rw [h0] at this
    simp at this
  have hinv : (starRingEnd ℂ) (e k) = (e k)⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, norm_e]
    simp
  rw [hinv, eq_comm]
  field_simp
  linear_combination h

/-- Expansion of a sum over `ZMod 5`. -/
lemma sum_zmod5 (g : ZMod 5 → ℂ) : ∑ x : ZMod 5, g x = g 0 + g 1 + g 2 + g 3 + g 4 := by
  have h : (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

lemma sum_e : ∑ x : ZMod 5, e x = 0 := by
  rw [sum_zmod5]
  have h1 : e 1 = omega := by rw [show (1 : ZMod 5) = ((1 : ℕ) : ZMod 5) by norm_num, e_natCast]; ring
  have h2 : e 2 = omega ^ 2 := by
    rw [show (2 : ZMod 5) = ((2 : ℕ) : ZMod 5) by norm_num, e_natCast]
  have h3 : e 3 = omega ^ 3 := by
    rw [show (3 : ZMod 5) = ((3 : ℕ) : ZMod 5) by norm_num, e_natCast]
  have h4 : e 4 = omega ^ 4 := by
    rw [show (4 : ZMod 5) = ((4 : ℕ) : ZMod 5) by norm_num, e_natCast]
  rw [e_zero, h1, h2, h3, h4]
  exact geom_sum_omega

/-- Orthogonality of the characters. -/
lemma sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [if_neg hk]
    have : ∑ a : ZMod 5, e (a * k) = ∑ b : ZMod 5, e b :=
      Fintype.sum_equiv (Equiv.mulRight₀ k hk) _ _ (fun a => rfl)
    rw [this, sum_e]

/-- The complex-valued core Parseval identity. -/
lemma parseval_core (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
  have key : ∀ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ x : ZMod 5, ∑ y : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (x - y)) := by
    intro a
    rw [dft, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, conj_e]
    have he : e (a * x) * e (-(a * y)) = e (a * (x - y)) := by
      rw [← e_add, show a * x + -(a * y) = a * (x - y) by ring]
    rw [← he]
    ring
  simp_rw [key]
  rw [Finset.sum_comm]
  have step : ∀ x : ZMod 5, ∑ a : ZMod 5, ∑ y : ZMod 5,
      f x * (starRingEnd ℂ) (f y) * e (a * (x - y))
      = 5 * (f x * (starRingEnd ℂ) (f x)) := by
    intro x
    rw [Finset.sum_comm]
    have : ∀ y : ZMod 5, ∑ a : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (x - y))
        = if y = x then 5 * (f x * (starRingEnd ℂ) (f x)) else 0 := by
      intro y
      rw [← Finset.mul_sum, sum_e_mul]
      by_cases hxy : y = x
      · subst hxy
        simp
        ring
      · rw [if_neg (by simpa [sub_eq_zero, eq_comm] using hxy), if_neg hxy, mul_zero]
    rw [Finset.sum_congr rfl fun y _ => this y, Finset.sum_ite_eq' Finset.univ x]
    simp
  rw [Finset.sum_congr rfl fun x _ => step x, ← Finset.mul_sum]

/-- **Parseval/Plancherel** on `ZMod 5` for the unnormalized discrete Fourier transform. -/
theorem parseval (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, ‖dft f a‖ ^ 2 = 5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 := by
  have hcast : ((∑ a : ZMod 5, ‖dft f a‖ ^ 2 : ℝ) : ℂ)
      = ((5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    have hL : ∀ z : ℂ, ((‖z‖ : ℂ)) ^ 2 = z * (starRingEnd ℂ) z := by
      intro z
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    simp_rw [hL]
    exact parseval_core f
  exact_mod_cast hcast

end Characters5
end Brockian

