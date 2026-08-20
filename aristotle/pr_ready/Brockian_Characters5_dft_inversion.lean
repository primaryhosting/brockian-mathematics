/-!
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
Statement: Fourier inversion on ZMod 5: with dft f a = Σ_x e(a*x) f(x), every f is recovered as f x = (1/5) Σ_a e(-(a*x)) * dft f a.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

lemma isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  have := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega] using this

lemma omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

/-- The additive character `k ↦ ω ^ k` on `ZMod 5`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

lemma omega_pow_mod (m : ℕ) : omega ^ (m % 5) = omega ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 5, pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma e_add (a b : ZMod 5) : e (a + b) = e a * e b := by
  rw [e, e, e, ZMod.val_add, omega_pow_mod, pow_add]

lemma sum_e_univ : ∑ b : ZMod 5, e b = 0 := by
  have h : ∑ b : ZMod 5, e b = ∑ j ∈ Finset.range 5, omega ^ j := by
    simp only [e]
    apply Finset.sum_nbij' (fun b : ZMod 5 => b.val) (fun j : ℕ => (j : ZMod 5)) <;>
      intros <;> simp_all [ZMod.val_lt]
  rw [h]
  exact isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

lemma sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (a * k) = if k = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hk : k = 0
  · subst hk
    simp [e]
  · rw [if_neg hk]
    rw [← sum_e_univ]
    exact Fintype.sum_equiv (Equiv.mulRight₀ k hk) _ _ (fun a => rfl)

/-- The discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) : ZMod 5 → ℂ := fun a => ∑ x : ZMod 5, e (a * x) * f x

theorem dft_inversion (f : ZMod 5 → ℂ) (x : ZMod 5) :
    f x = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (-(a * x)) * dft f a := by
  have key : ∀ a : ZMod 5,
      e (-(a * x)) * dft f a = ∑ y : ZMod 5, e (a * (y - x)) * f y := by
    intro a
    rw [dft, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hchar : e (-(a * x)) * e (a * y) = e (a * (y - x)) := by
      rw [← e_add]; congr 1; ring
    rw [← mul_assoc, hchar]
  symm
  calc (1 / 5 : ℂ) * ∑ a : ZMod 5, e (-(a * x)) * dft f a
      = (1 / 5 : ℂ) * ∑ a : ZMod 5, ∑ y : ZMod 5, e (a * (y - x)) * f y := by
        rw [Finset.sum_congr rfl fun a _ => key a]
    _ = (1 / 5 : ℂ) * ∑ y : ZMod 5, (∑ a : ZMod 5, e (a * (y - x))) * f y := by
        rw [Finset.sum_comm]
        simp [Finset.sum_mul]
    _ = (1 / 5 : ℂ) * ∑ y : ZMod 5, (if y = x then (5 : ℂ) else 0) * f y := by
        refine congrArg _ (Finset.sum_congr rfl fun y _ => ?_)
        rw [sum_e_mul]
        simp [sub_eq_zero]
    _ = f x := by
        simp

end Brockian.Characters5

