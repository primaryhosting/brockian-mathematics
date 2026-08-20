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

set_option grind.warning false

namespace Chem

open Polynomial

/-- A primitive 8-th root of unity. -/

theorem sum_w8 (d : Fin 8) : (∑ j : Fin 8, w8 (j * d)) = if d = 0 then 8 else 0 := by
  by_cases hd : d = 0
  · subst hd
    simp [w8_zero]
  · rw [if_neg hd]
    set S : ℂ := ∑ j : Fin 8, w8 (j * d) with hS
    have hshift : w8 d * S = S := by
      have hstep : w8 d * S = ∑ j : Fin 8, w8 ((j + 1) * d) := by
        rw [hS, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [add_mul, one_mul, w8_add, mul_comm]
      rw [hstep]
      exact Fintype.sum_equiv (Equiv.addRight (1 : Fin 8)) _ _ (fun _ => rfl)
    have h1 : (w8 d - 1) * S = 0 := by linear_combination hshift
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (by linear_combination h) (w8_ne_one hd)
    · exact h

/-- Euler's formula, in the form `ζ₈ᵏ + ζ₈⁻ᵏ = 2 cos (2πk/8)`. -/
