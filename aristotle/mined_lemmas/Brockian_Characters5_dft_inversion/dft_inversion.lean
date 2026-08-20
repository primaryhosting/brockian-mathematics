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

