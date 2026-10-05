/-
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Brockian.Characters5

/-- The primitive fifth root of unity `exp (2πi/5)`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5`, `e k = ω ^ k`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

/-- The unnormalized discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) (a : ZMod 5) : ℂ := ∑ x : ZMod 5, f x * e (a * x)

lemma isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 :=
  Complex.isPrimitiveRoot_exp 5 (by norm_num)

lemma omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

lemma omega_pow_mod (m : ℕ) : omega ^ (m % 5) = omega ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 5, pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_add (k l : ZMod 5) : e (k + l) = e k * e l := by
  simp only [e, ZMod.val_add, omega_pow_mod, pow_add]

lemma e_mul_e_neg (k : ZMod 5) : e k * e (-k) = 1 := by
  rw [← e_add]; simp [e_zero]

lemma norm_e (k : ZMod 5) : ‖e k‖ = 1 := by
  have h : ‖omega‖ = 1 := by
    have hrw : omega = Complex.exp (((2 * Real.pi / 5 : ℝ) : ℂ) * Complex.I) := by
      rw [omega]; push_cast; ring_nf
    rw [hrw, Complex.norm_exp_ofReal_mul_I]
  simp [e, norm_pow, h]

lemma conj_e (k : ZMod 5) : (starRingEnd ℂ) (e k) = e (-k) := by
  have hne : e k ≠ 0 := by
    intro h
    have := norm_e k
    rw [h] at this
    simp at this
  have h1 : e k * (starRingEnd ℂ) (e k) = 1 := by
    rw [Complex.mul_conj', norm_e]
    norm_num
  have h2 : e k * e (-k) = 1 := e_mul_e_neg k
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

lemma sum_omega_pow : ∑ i ∈ Finset.range 5, omega ^ i = 0 :=
  isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

lemma sum_e : ∑ k : ZMod 5, e k = 0 := by
  have : ∑ k : ZMod 5, e k = ∑ i ∈ Finset.range 5, omega ^ i := by
    show ∑ k : Fin 5, omega ^ (ZMod.val (n := 5) k) = _
    simp [ZMod.val, Fin.sum_univ_five, Finset.sum_range_succ]
  rw [this, sum_omega_pow]

lemma sum_e_mul (n : ZMod 5) : ∑ k : ZMod 5, e (k * n) = if n = 0 then 5 else 0 := by
  by_cases hn : n = 0
  · subst hn
    simp [e_zero]
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [if_neg hn, ← sum_e]
    exact Fintype.sum_equiv (Equiv.mulRight₀ n hn) _ _ (fun k => rfl)

/-- The complex-valued core Parseval identity. -/
lemma parseval_core (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
  have expand : ∀ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ x : ZMod 5, ∑ y : ZMod 5,
          (f x * (starRingEnd ℂ) (f y)) * e (a * (x - y)) := by
    intro a
    rw [dft, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [map_mul, conj_e]
    have : e (a * x) * e (-(a * y)) = e (a * (x - y)) := by
      rw [← e_add]; ring_nf
    rw [← this]; ring
  calc ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ a : ZMod 5, ∑ x : ZMod 5, ∑ y : ZMod 5,
          (f x * (starRingEnd ℂ) (f y)) * e (a * (x - y)) := by
        exact Finset.sum_congr rfl (fun a _ => expand a)
    _ = ∑ x : ZMod 5, ∑ y : ZMod 5, (f x * (starRingEnd ℂ) (f y)) *
          ∑ a : ZMod 5, e (a * (x - y)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun y _ => by rw [Finset.mul_sum])
    _ = ∑ x : ZMod 5, ∑ y : ZMod 5, (f x * (starRingEnd ℂ) (f y)) *
          (if y = x then (5 : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
        rw [sum_e_mul]
        congr 1
        by_cases h : y = x
        · simp [h]
        · rw [if_neg h, if_neg (fun hc : x - y = 0 => h (sub_eq_zero.mp hc).symm)]
    _ = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        have h : ∀ y : ZMod 5, (f x * (starRingEnd ℂ) (f y)) * (if y = x then (5 : ℂ) else 0)
            = if y = x then 5 * (f x * (starRingEnd ℂ) (f x)) else 0 := by
          intro y
          by_cases hy : y = x
          · simp [hy]; ring
          · simp [hy]
        simp only [h, Finset.sum_ite_eq' Finset.univ x, Finset.mem_univ, if_true]

theorem parseval (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, ‖dft f a‖ ^ 2 = 5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 := by
  have h := parseval_core f
  simp only [Complex.mul_conj'] at h
  have : ((∑ a : ZMod 5, ‖dft f a‖ ^ 2 : ℝ) : ℂ)
      = ((5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact h
  exact_mod_cast this

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

