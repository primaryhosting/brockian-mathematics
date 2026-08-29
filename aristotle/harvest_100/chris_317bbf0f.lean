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
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `k ↦ ω ^ k` on `ZMod 5`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

/-- The (unnormalized) discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) (a : ZMod 5) : ℂ := ∑ x : ZMod 5, f x * e (a * x)

theorem isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  have := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega] using this

theorem omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

theorem omega_pow_mod (n : ℕ) : omega ^ (n % 5) = omega ^ n := by
  conv_rhs => rw [show n = 5 * (n / 5) + n % 5 by omega]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

theorem e_zero : e 0 = 1 := by simp [e]

theorem e_add (j k : ZMod 5) : e (j + k) = e j * e k := by
  simp only [e, ZMod.val_add, omega_pow_mod, pow_add]

theorem norm_omega : ‖omega‖ = 1 := by
  have h : omega = Complex.exp ((2 * Real.pi / 5 : ℝ) * Complex.I) := by
    rw [omega]
    push_cast
    ring_nf
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem norm_e (k : ZMod 5) : ‖e k‖ = 1 := by
  simp [e, norm_pow, norm_omega]

theorem e_ne_zero (k : ZMod 5) : e k ≠ 0 := by
  intro h
  have := norm_e k
  rw [h] at this
  simp at this

theorem conj_e (k : ZMod 5) : (starRingEnd ℂ) (e k) = e (-k) := by
  have h1 : e k * (starRingEnd ℂ) (e k) = 1 := by
    rw [Complex.mul_conj', norm_e]; norm_num
  have h2 : e k * e (-k) = 1 := by
    rw [← e_add]; simp [e_zero]
  exact mul_left_cancel₀ (e_ne_zero k) (h1.trans h2.symm)

theorem sum_e : (∑ a : ZMod 5, e a) = 0 := by
  rw [show (∑ a : ZMod 5, e a) = ∑ a : Fin 5, omega ^ (a : ℕ) from rfl,
    Fin.sum_univ_eq_sum_range]
  exact isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

theorem sum_e_mul (k : ZMod 5) : (∑ a : ZMod 5, e (a * k)) = if k = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hk : k = 0
  · subst hk
    simp [e_zero]
  · rw [if_neg hk]
    rw [Fintype.sum_equiv (Equiv.mulRight₀ k hk) (fun a => e (a * k)) e (fun a => rfl)]
    exact sum_e

theorem parseval_core (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
  have expand : ∀ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ x : ZMod 5, ∑ y : ZMod 5, (f x * (starRingEnd ℂ) (f y)) * e (a * (x - y)) := by
    intro a
    rw [dft, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [map_mul, conj_e]
    have : e (a * x) * e (-(a * y)) = e (a * (x - y)) := by
      rw [← e_add]; ring_nf
    calc f x * e (a * x) * ((starRingEnd ℂ) (f y) * e (-(a * y)))
        = (f x * (starRingEnd ℂ) (f y)) * (e (a * x) * e (-(a * y))) := by ring
      _ = f x * (starRingEnd ℂ) (f y) * e (a * (x - y)) := by rw [this]
  calc ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ a : ZMod 5, ∑ x : ZMod 5, ∑ y : ZMod 5,
          (f x * (starRingEnd ℂ) (f y)) * e (a * (x - y)) :=
        Finset.sum_congr rfl (fun a _ => expand a)
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
        · rw [if_neg h, if_neg (by intro hc; exact h (by linear_combination -hc))]
    _ = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x)]
        · rw [if_pos rfl]; ring
        · intro y _ hy
          rw [if_neg hy, mul_zero]

theorem parseval (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, ‖dft f a‖ ^ 2 = 5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 := by
  have h := parseval_core f
  simp only [Complex.mul_conj'] at h
  have : ((∑ a : ZMod 5, ‖dft f a‖ ^ 2 : ℝ) : ℂ) = ((5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact h
  exact_mod_cast this

end Brockian.Characters5

