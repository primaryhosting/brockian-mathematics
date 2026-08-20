/-
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
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

namespace Brockian

namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `k ↦ ω ^ k` on `ZMod 5`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

/-- The (unnormalized) discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) (a : ZMod 5) : ℂ := ∑ x : ZMod 5, f x * e (-(a * x))

theorem isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  have := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega] using this

theorem omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

theorem norm_omega : ‖omega‖ = 1 := by
  simp [omega, Complex.norm_exp]

theorem omega_pow_mod (n : ℕ) : omega ^ (n % 5) = omega ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

theorem e_add (k j : ZMod 5) : e (k + j) = e k * e j := by
  simp only [e, ZMod.val_add, omega_pow_mod, pow_add]

theorem e_zero : e 0 = 1 := by simp [e]

theorem norm_e (k : ZMod 5) : ‖e k‖ = 1 := by
  simp [e, norm_pow, norm_omega]

theorem e_ne_zero (k : ZMod 5) : e k ≠ 0 := by
  intro h
  have := norm_e k
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem conj_e (k : ZMod 5) : (starRingEnd ℂ) (e k) = e (-k) := by
  have h1 : e k * e (-k) = 1 := by rw [← e_add]; simp [e_zero]
  have h2 : (starRingEnd ℂ) (e k) * e k = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_e]
    norm_num
  calc (starRingEnd ℂ) (e k) = (starRingEnd ℂ) (e k) * (e k * e (-k)) := by
        rw [h1, mul_one]
    _ = (starRingEnd ℂ) (e k) * e k * e (-k) := by ring
    _ = e (-k) := by rw [h2, one_mul]

theorem e_nsmul (k : ZMod 5) (n : ℕ) : e (n • k) = e k ^ n := by
  induction n with
  | zero => simp [e_zero]
  | succ m ih => rw [succ_nsmul, e_add, ih, pow_succ]

theorem e_mul_val (a k : ZMod 5) : e (a * k) = e k ^ a.val := by
  rw [← e_nsmul, nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]

theorem e_pow_five (k : ZMod 5) : e k ^ 5 = 1 := by
  rw [← e_nsmul]
  have h : (5 : ℕ) • k = 0 := by
    rw [nsmul_eq_mul, show ((5 : ℕ) : ZMod 5) = 0 by decide, zero_mul]
  rw [h, e_zero]

theorem e_ne_one (k : ZMod 5) (hk : k ≠ 0) : e k ≠ 1 :=
  isPrimitiveRoot_omega.pow_ne_one_of_pos_of_lt
    (fun h => hk ((ZMod.val_eq_zero k).mp h)) (ZMod.val_lt k)

/-- Orthogonality of the characters on `ZMod 5`. -/
theorem sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  have hexp : ∑ a : ZMod 5, e (a * k) = 1 + e k + e k ^ 2 + e k ^ 3 + e k ^ 4 := by
    have hval : ∀ a : ZMod 5, e (a * k) = e k ^ a.val := fun a => e_mul_val a k
    simp only [hval]
    show ∑ a : Fin 5, e k ^ (ZMod.val (n := 5) a) = _
    rw [Fin.sum_univ_five]
    norm_num [show ZMod.val (1 : ZMod 5) = 1 from by decide,
      show ZMod.val (2 : ZMod 5) = 2 from by decide,
      show ZMod.val (3 : ZMod 5) = 3 from by decide,
      show ZMod.val (4 : ZMod 5) = 4 from by decide]
  rw [hexp]
  by_cases hk : k = 0
  · rw [if_pos hk, hk, e_zero]
    norm_num
  · rw [if_neg hk]
    have h5 : e k ^ 5 = 1 := e_pow_five k
    have hz := e_ne_one k hk
    have hfac : (e k - 1) * (1 + e k + e k ^ 2 + e k ^ 3 + e k ^ 4) = 0 := by
      linear_combination h5
    rcases mul_eq_zero.1 hfac with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) hz
    · exact h1

/-- The complex-valued core of Parseval's identity. -/
theorem parseval_core (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
  have step1 : ∀ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ x : ZMod 5, ∑ y : ZMod 5,
          (f x * (starRingEnd ℂ) (f y)) * e (a * (y - x)) := by
    intro a
    rw [dft, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [map_mul, conj_e, neg_neg]
    rw [show a * (y - x) = -(a * x) + a * y by ring, e_add]
    ring
  rw [Finset.sum_congr rfl (fun a _ => step1 a)]
  rw [Finset.sum_comm]
  have step2 : ∀ x : ZMod 5,
      ∑ a : ZMod 5, ∑ y : ZMod 5, (f x * (starRingEnd ℂ) (f y)) * e (a * (y - x))
        = 5 * (f x * (starRingEnd ℂ) (f x)) := by
    intro x
    rw [Finset.sum_comm]
    have : ∀ y : ZMod 5, ∑ a : ZMod 5, (f x * (starRingEnd ℂ) (f y)) * e (a * (y - x))
        = (f x * (starRingEnd ℂ) (f y)) * (if y - x = 0 then 5 else 0) := by
      intro y
      rw [← Finset.mul_sum, sum_e_mul]
    rw [Finset.sum_congr rfl (fun y _ => this y)]
    have heq : ∀ y : ZMod 5, (f x * (starRingEnd ℂ) (f y)) * (if y - x = 0 then (5:ℂ) else 0)
        = if y = x then 5 * (f x * (starRingEnd ℂ) (f x)) else 0 := by
      intro y
      by_cases hy : y = x
      · subst hy; rw [sub_self, if_pos rfl, if_pos rfl]; ring
      · rw [if_neg hy, if_neg (fun h => hy (by rwa [sub_eq_zero] at h)), mul_zero]
    rw [Finset.sum_congr rfl (fun y _ => heq y), Finset.sum_ite_eq' Finset.univ x]
    simp
  rw [Finset.sum_congr rfl (fun x _ => step2 x), ← Finset.mul_sum]

theorem parseval (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, ‖dft f a‖ ^ 2 = 5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 := by
  have h := parseval_core f
  have hL : ∀ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a) = ((‖dft f a‖ ^ 2 : ℝ) : ℂ) := by
    intro a; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hR : ∀ x : ZMod 5, f x * (starRingEnd ℂ) (f x) = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    intro x; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hL, hR] at h
  rw [← Complex.ofReal_sum] at h
  rw [← Complex.ofReal_sum] at h
  have h' : ((∑ a : ZMod 5, ‖dft f a‖ ^ 2 : ℝ) : ℂ)
      = ((5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [h]; push_cast; ring
  exact_mod_cast h'

end Characters5

end Brockian

