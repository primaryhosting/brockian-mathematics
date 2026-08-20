import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₅`, i.e. the Hückel matrix of
cyclopentadienyl (with `α = 0`, `β = 1`). -/

lemma quintic_root_iff (t : ℝ) :
    t^5 - 5*t^3 + 5*t - 2 = 0 ↔
      t = 2 ∨ t = (Real.sqrt 5 - 1)/2 ∨ t = -(1 + Real.sqrt 5)/2 := by
  have hfac : t^5 - 5*t^3 + 5*t - 2
      = (t - 2) * ((t - (Real.sqrt 5 - 1)/2) * (t + (1 + Real.sqrt 5)/2))^2 := by
    have h : (t - (Real.sqrt 5 - 1)/2) * (t + (1 + Real.sqrt 5)/2) = t^2 + t - 1 := by
      linear_combination (-1/4 : ℝ) * sqrt_five_sq
    rw [h]; ring
  rw [hfac]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (by linarith [sub_eq_zero.1 h])
    · have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact Or.inr (Or.inl (by linarith [sub_eq_zero.1 h'']))
      · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> ring

