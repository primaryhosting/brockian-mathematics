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

/-
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

lemma isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega] using h

lemma omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

/-- The additive character `k ↦ ω ^ k` on `ZMod 5`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

/-- The (unnormalized) discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) (a : ZMod 5) : ℂ := ∑ x : ZMod 5, f x * e (a * x)

lemma omega_pow_mod (n : ℕ) : omega ^ (n % 5) = omega ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_add (k l : ZMod 5) : e (k + l) = e k * e l := by
  simp only [e, ZMod.val_add, omega_pow_mod, pow_add]

lemma e_neg_mul_self (k : ZMod 5) : e k * e (-k) = 1 := by
  rw [← e_add]; simp [e_zero]

lemma e_ne_zero (k : ZMod 5) : e k ≠ 0 := by
  intro h
  have h1 := e_neg_mul_self k
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

lemma norm_e (k : ZMod 5) : ‖e k‖ = 1 := by
  have h : ‖omega‖ = 1 := isPrimitiveRoot_omega.norm'_eq_one (by norm_num)
  simp [e, norm_pow, h]

lemma conj_e (k : ZMod 5) : (starRingEnd ℂ) (e k) = e (-k) := by
  have h1 : (starRingEnd ℂ) (e k) * e k = 1 := by
    rw [mul_comm, Complex.mul_conj', norm_e]
    norm_num
  have h2 : e (-k) * e k = 1 := by rw [mul_comm]; exact e_neg_mul_self k
  exact mul_right_cancel₀ (e_ne_zero k) (h1.trans h2.symm)

lemma sum_omega_pow : ∑ i ∈ Finset.range 5, omega ^ i = 0 :=
  isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

lemma sum_e_univ : ∑ b : ZMod 5, e b = 0 := by
  have h5 := sum_omega_pow
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one] at h5
  have h : ∑ b : ZMod 5, e b = omega ^ 0 + omega ^ 1 + omega ^ 2 + omega ^ 3 + omega ^ 4 := by
    show ∑ b : Fin 5, e b = _
    rw [Fin.sum_univ_five]
    rfl
  rw [h, h5]

/-- Orthogonality of the characters. -/
lemma sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hk : k = 0
  · subst hk
    simp [e, ZMod.card]
  · rw [if_neg hk]
    have h : ∑ a : ZMod 5, e (a * k) = ∑ b : ZMod 5, e b :=
      Fintype.sum_equiv (Equiv.mulRight₀ k hk) _ _ (fun a => rfl)
    rw [h, sum_e_univ]

/-- The complex-valued core of Parseval's identity. -/
lemma parseval_core (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
  have expand : ∀ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ x : ZMod 5, ∑ y : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (x - y)) := by
    intro a
    rw [dft, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [map_mul, conj_e]
    have hmul : e (a * x) * e (-(a * y)) = e (a * (x - y)) := by
      rw [← e_add]; ring_nf
    calc f x * e (a * x) * ((starRingEnd ℂ) (f y) * e (-(a * y)))
        = f x * (starRingEnd ℂ) (f y) * (e (a * x) * e (-(a * y))) := by ring
      _ = f x * (starRingEnd ℂ) (f y) * e (a * (x - y)) := by rw [hmul]
  calc ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ a : ZMod 5, ∑ x : ZMod 5, ∑ y : ZMod 5,
          f x * (starRingEnd ℂ) (f y) * e (a * (x - y)) :=
        Finset.sum_congr rfl (fun a _ => expand a)
    _ = ∑ x : ZMod 5, ∑ y : ZMod 5, f x * (starRingEnd ℂ) (f y) *
          ∑ a : ZMod 5, e (a * (x - y)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ x : ZMod 5, ∑ y : ZMod 5, (if y = x then f x * (starRingEnd ℂ) (f y) * 5 else 0) := by
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
        rw [sum_e_mul]
        by_cases h : y = x
        · subst h; simp
        · rw [if_neg h, if_neg (fun hc : x - y = 0 => h (by linear_combination -hc)), mul_zero]
    _ = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_ite_eq' Finset.univ x (fun y => f x * (starRingEnd ℂ) (f y) * 5)]
        simp [mul_comm]

/-- Parseval/Plancherel identity on `ZMod 5` for the unnormalized transform. -/
theorem parseval (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, ‖dft f a‖ ^ 2 = 5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 := by
  have h := parseval_core f
  simp only [Complex.mul_conj'] at h
  have h2 : ((∑ a : ZMod 5, ‖dft f a‖ ^ 2 : ℝ) : ℂ)
      = ((5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact h
  exact_mod_cast h2

end Characters5
end Brockian

