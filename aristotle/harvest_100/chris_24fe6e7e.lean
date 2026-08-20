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

namespace Brockian.Characters5

/-- The primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` given by `k ↦ ω ^ k`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

lemma omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  rw [show ((5 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I by
    push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma omega_ne_one : omega ≠ 1 := by
  intro h
  rw [omega, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have h5 : (5 : ℂ) * n = 1 := by
    field_simp at hn
    linear_combination -hn
  have : ((5 * n : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by push_cast; linear_combination h5
  have h5' : (5 : ℤ) * n = 1 := by exact_mod_cast this
  omega

lemma omega_pow_mod (n : ℕ) : omega ^ (n % 5) = omega ^ n := by
  conv_rhs => rw [show n = 5 * (n / 5) + n % 5 by omega]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma e_add (a b : ZMod 5) : e (a + b) = e a * e b := by
  simp only [e, ZMod.val_add, omega_pow_mod, pow_add]

lemma e_zero : e 0 = 1 := by
  simp [e]

/-- The sum of all values of the character over `ZMod 5` vanishes. -/
lemma sum_e : ∑ b : ZMod 5, e b = 0 := by
  have hexp : ∑ b : ZMod 5, e b = 1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 := by
    have h1 : ZMod.val (1 : ZMod 5) = 1 := rfl
    have h2 : ZMod.val (2 : ZMod 5) = 2 := rfl
    have h3 : ZMod.val (3 : ZMod 5) = 3 := rfl
    have h4 : ZMod.val (4 : ZMod 5) = 4 := rfl
    simp only [e]
    rw [show (∑ b : ZMod 5, omega ^ b.val)
        = omega ^ ZMod.val (0 : ZMod 5) + omega ^ ZMod.val (1 : ZMod 5)
          + omega ^ ZMod.val (2 : ZMod 5) + omega ^ ZMod.val (3 : ZMod 5)
          + omega ^ ZMod.val (4 : ZMod 5) from by
      simp [Fin.sum_univ_five, ZMod]]
    rw [h1, h2, h3, h4]
    norm_num
  have hkey : (omega - 1) * (1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4) = 0 := by
    have := omega_pow_five
    linear_combination this
  have hne : omega - 1 ≠ 0 := sub_ne_zero.mpr omega_ne_one
  rw [hexp]
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h hne
  · exact h

/-- Orthogonality of characters on `ZMod 5`. -/
lemma sum_e_mul (k : ZMod 5) : ∑ a : ZMod 5, e (k * a) = if k = 0 then 5 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [e_zero]
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [if_neg hk]
    have : ∑ a : ZMod 5, e (k * a) = ∑ b : ZMod 5, e b :=
      Fintype.sum_equiv (Equiv.mulLeft₀ k hk) _ _ (fun a => rfl)
    rw [this, sum_e]

/-- The discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) : ZMod 5 → ℂ := fun a => ∑ x : ZMod 5, e (a * x) * f x

/-- Fourier inversion on `ZMod 5`. -/
theorem dft_inversion (f : ZMod 5 → ℂ) (x : ZMod 5) :
    f x = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (-(a * x)) * dft f a := by
  have hstep : ∀ a : ZMod 5, e (-(a * x)) * dft f a = ∑ y : ZMod 5, e ((y - x) * a) * f y := by
    intro a
    rw [dft, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← mul_assoc, ← e_add]
    ring_nf
  symm
  calc (1 / 5 : ℂ) * ∑ a : ZMod 5, e (-(a * x)) * dft f a
      = (1 / 5 : ℂ) * ∑ a : ZMod 5, ∑ y : ZMod 5, e ((y - x) * a) * f y := by
        rw [Finset.sum_congr rfl (fun a _ => hstep a)]
    _ = (1 / 5 : ℂ) * ∑ y : ZMod 5, (∑ a : ZMod 5, e ((y - x) * a)) * f y := by
        rw [Finset.sum_comm]
        simp [Finset.sum_mul]
    _ = (1 / 5 : ℂ) * ∑ y : ZMod 5, (if y - x = 0 then (5 : ℂ) else 0) * f y := by
        refine congrArg _ (Finset.sum_congr rfl (fun y _ => ?_))
        rw [sum_e_mul]
    _ = f x := by
        have : ∀ y : ZMod 5, (if y - x = 0 then (5 : ℂ) else 0) * f y
            = if y = x then 5 * f x else 0 := by
          intro y
          by_cases h : y = x
          · simp [h]
          · simp [sub_eq_zero, h]
        rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_ite_eq' Finset.univ x
          (fun _ => (5 : ℂ) * f x)]
        simp

end Brockian.Characters5
#print axioms Brockian.Characters5.dft_inversion

