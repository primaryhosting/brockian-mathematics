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

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` associated with `ω`. -/
noncomputable def e (k : ZMod 5) : ℂ := ω ^ k.val

/-- The (unnormalized) discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) (a : ZMod 5) : ℂ := ∑ x : ZMod 5, f x * e (-(a * x))

theorem isPrimitiveRoot_omega : IsPrimitiveRoot ω 5 := by
  simpa [ω] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

theorem omega_pow_five : ω ^ (5 : ℕ) = 1 := isPrimitiveRoot_omega.pow_eq_one

theorem omega_pow_mod (n : ℕ) : ω ^ (n % 5) = ω ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

theorem e_zero : e 0 = 1 := by simp [e]

theorem e_add (j k : ZMod 5) : e (j + k) = e j * e k := by
  simp only [e, ZMod.val_add, omega_pow_mod, pow_add]

theorem norm_e (k : ZMod 5) : ‖e k‖ = 1 := by
  have h : ‖ω‖ = 1 := by
    simp [ω, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  simp [e, norm_pow, h]

theorem e_conj (k : ZMod 5) : (starRingEnd ℂ) (e k) = e (-k) := by
  have h1 : e k * e (-k) = 1 := by rw [← e_add]; simp [e_zero]
  have hne : e k ≠ 0 := by
    intro h
    have := norm_e k
    rw [h] at this
    simp at this
  have h2 : e k * (starRingEnd ℂ) (e k) = 1 := by
    rw [Complex.mul_conj']
    have := norm_e k
    rw [this]
    norm_num
  exact mul_left_cancel₀ hne (h2.trans h1.symm)

/-- Orthogonality of the characters. -/
theorem sum_e_mul (k : ZMod 5) :
    ∑ a : ZMod 5, e (a * k) = if k = 0 then (5 : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [e_zero]
  · rw [if_neg hk]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hbij : ∑ a : ZMod 5, e (a * k) = ∑ b : ZMod 5, e b := by
      refine Fintype.sum_bijective (fun a => a * k) ?_ _ _ (fun a => rfl)
      exact (Equiv.mulRight₀ k hk).bijective
    rw [hbij]
    have : ∑ b : ZMod 5, e b = ∑ i ∈ Finset.range 5, ω ^ i := by
      rw [show (Finset.univ : Finset (ZMod 5)) = Finset.univ from rfl]
      rw [← Fin.sum_univ_eq_sum_range (fun i => ω ^ i) 5]
      rfl
    rw [this]
    exact isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

/-- The complex-valued core Parseval identity. -/
theorem parseval_core (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
  have expand : ∀ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ x : ZMod 5, ∑ y : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (y - x)) := by
    intro a
    rw [dft, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [map_mul, e_conj]
    have : e (-(a * x)) * e (-(-(a * y))) = e (a * (y - x)) := by
      rw [← e_add]; ring_nf
    calc f x * e (-(a * x)) * ((starRingEnd ℂ) (f y) * e (-(-(a * y))))
        = f x * (starRingEnd ℂ) (f y) * (e (-(a * x)) * e (-(-(a * y)))) := by ring
      _ = f x * (starRingEnd ℂ) (f y) * e (a * (y - x)) := by rw [this]
  rw [Finset.sum_congr rfl (fun a _ => expand a)]
  rw [Finset.sum_comm]
  have step : ∀ x : ZMod 5,
      ∑ a : ZMod 5, ∑ y : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (y - x))
        = 5 * (f x * (starRingEnd ℂ) (f x)) := by
    intro x
    rw [Finset.sum_comm]
    have : ∀ y : ZMod 5, ∑ a : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (y - x))
        = f x * (starRingEnd ℂ) (f y) * (if y - x = 0 then (5 : ℂ) else 0) := by
      intro y
      rw [← Finset.mul_sum, sum_e_mul]
    rw [Finset.sum_congr rfl (fun y _ => this y)]
    have : ∀ y : ZMod 5, f x * (starRingEnd ℂ) (f y) * (if y - x = 0 then (5 : ℂ) else 0)
        = if y = x then 5 * (f x * (starRingEnd ℂ) (f x)) else 0 := by
      intro y
      by_cases hy : y = x
      · subst hy; simp; ring
      · have : y - x ≠ 0 := sub_ne_zero_of_ne hy
        simp [hy, this]
    rw [Finset.sum_congr rfl (fun y _ => this y)]
    simp
  rw [Finset.sum_congr rfl (fun x _ => step x), ← Finset.mul_sum]

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

