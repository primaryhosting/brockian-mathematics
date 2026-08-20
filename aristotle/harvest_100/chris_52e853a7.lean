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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

lemma omega_isPrimitiveRoot : IsPrimitiveRoot ω 5 := by
  have := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [ω] using this

lemma omega_pow_five : ω ^ 5 = 1 := omega_isPrimitiveRoot.pow_eq_one

/-- The additive character `e` on `ZMod 5`. -/
noncomputable def e (k : ZMod 5) : ℂ := ω ^ k.val

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_add (a b : ZMod 5) : e (a + b) = e a * e b := by
  have hval : (a + b).val = (a.val + b.val) % 5 := ZMod.val_add a b
  have h : ω ^ (a.val + b.val) = ω ^ ((a.val + b.val) % 5) := by
    conv_lhs => rw [← Nat.div_add_mod (a.val + b.val) 5]
    rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]
  simp only [e, hval, ← pow_add, h]

lemma e_neg_mul_self (k : ZMod 5) : e (-k) * e k = 1 := by
  rw [← e_add, neg_add_cancel, e_zero]

lemma sum_e : ∑ a : ZMod 5, e a = 0 := by
  have hgeom : ∑ i ∈ Finset.range 5, ω ^ i = 0 :=
    omega_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
  have : ∑ a : ZMod 5, e a = ∑ i ∈ Finset.range 5, ω ^ i := by
    rw [Finset.sum_range fun i => ω ^ i]
    rfl
  rw [this, hgeom]

lemma sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [e_zero, ZMod.card]
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [if_neg hk]
    have := Equiv.sum_comp (Equiv.mulRight₀ k hk) e
    simpa [Equiv.mulRight₀, sum_e] using this

/-- The discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) : ZMod 5 → ℂ := fun a => ∑ x : ZMod 5, e (a * x) * f x

/-- Fourier inversion on `ZMod 5`. -/
theorem dft_inversion (f : ZMod 5 → ℂ) (x : ZMod 5) :
    f x = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (-(a * x)) * dft f a := by
  have hchar : ∀ a y : ZMod 5, e (a * (y - x)) = e (-(a * x)) * e (a * y) := by
    intro a y
    rw [← e_add]
    congr 1
    ring
  have key : ∑ a : ZMod 5, e (-(a * x)) * dft f a
      = ∑ y : ZMod 5, f y * ∑ a : ZMod 5, e (a * (y - x)) := by
    calc ∑ a : ZMod 5, e (-(a * x)) * dft f a
        = ∑ a : ZMod 5, ∑ y : ZMod 5, e (a * (y - x)) * f y := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [dft, Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hchar a y]
          ring
      _ = ∑ y : ZMod 5, ∑ a : ZMod 5, e (a * (y - x)) * f y := Finset.sum_comm
      _ = ∑ y : ZMod 5, f y * ∑ a : ZMod 5, e (a * (y - x)) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.sum_mul]
          ring
  rw [key]
  have : ∀ y : ZMod 5, f y * ∑ a : ZMod 5, e (a * (y - x))
      = if y = x then 5 * f x else 0 := by
    intro y
    rw [sum_e_mul]
    by_cases h : y = x
    · subst h; simp [mul_comm]
    · rw [if_neg (fun hc => h (sub_eq_zero.mp hc)), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl fun y _ => this y, Finset.sum_ite_eq' Finset.univ x
    (fun _ => (5 : ℂ) * f x)]
  simp

end Characters5
end Brockian

