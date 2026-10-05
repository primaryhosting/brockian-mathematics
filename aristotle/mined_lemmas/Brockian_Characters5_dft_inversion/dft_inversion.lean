/-
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

theorem dft_inversion (f : ZMod 5 → ℂ) (x : ZMod 5) :
    f x = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (-(a * x)) * dft f a := by
  have key : ∑ a : ZMod 5, e (-(a * x)) * dft f a
      = ∑ y : ZMod 5, f y * (if y - x = 0 then (5 : ℂ) else 0) := by
    simp only [dft, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : ∀ a : ZMod 5, e (-(a * x)) * (e (a * y) * f y) = e (a * (y - x)) * f y := by
      intro a
      rw [← mul_assoc, ← e_add]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun a _ => this a), ← Finset.sum_mul, sum_e_mul, mul_comm]
  rw [key]
  have : ∀ y : ZMod 5, f y * (if y - x = 0 then (5 : ℂ) else 0)
      = if y = x then f y * 5 else 0 := by
    intro y
    by_cases h : y = x
    · simp [h]
    · rw [if_neg h, if_neg (fun hc => h (sub_eq_zero.1 hc)), mul_zero]
  rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_ite_eq' Finset.univ x (fun y => f y * 5)]
  rw [if_pos (Finset.mem_univ x)]
  ring

end Brockian.Characters5

