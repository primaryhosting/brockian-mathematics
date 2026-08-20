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

/-- The primitive fifth root of unity `exp (2πi/5)`. -/

lemma parseval_core (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
  have hexp : ∀ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ x : ZMod 5, ∑ y : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (y - x)) := by
    intro a
    rw [dft, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    have key : e (-(a * x)) * e (- -(a * y)) = e (a * (y - x)) := by
      rw [← e_add]; congr 1; ring
    rw [map_mul, conj_e]
    linear_combination (f x * (starRingEnd ℂ) (f y)) * key
  rw [Finset.sum_congr rfl (fun a _ => hexp a)]
  rw [Finset.sum_comm]
  have : ∀ x : ZMod 5, ∑ a : ZMod 5, ∑ y : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (y - x))
      = 5 * (f x * (starRingEnd ℂ) (f x)) := by
    intro x
    rw [Finset.sum_comm]
    have hin : ∀ y : ZMod 5, ∑ a : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (y - x))
        = if y = x then 5 * (f x * (starRingEnd ℂ) (f y)) else 0 := by
      intro y
      rw [← Finset.mul_sum]
      have : ∑ a : ZMod 5, e (a * (y - x)) = if y - x = 0 then 5 else 0 := by
        rw [← sum_e_mul (y - x)]
        exact Finset.sum_congr rfl (fun a _ => by rw [mul_comm])
      rw [this]
      by_cases h : y = x
      · subst h; simp [mul_comm]
      · have : y - x ≠ 0 := sub_ne_zero_of_ne h
        simp [this, h]
    rw [Finset.sum_congr rfl (fun y _ => hin y), Finset.sum_ite_eq' Finset.univ x]
    simp
  rw [Finset.sum_congr rfl (fun x _ => this x), ← Finset.mul_sum]

/-- Parseval/Plancherel on `ZMod 5` for the unnormalized transform. -/
