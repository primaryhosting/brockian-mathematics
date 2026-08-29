/-
Auxiliary ordinal arithmetic: additive principality of `ω ^ γ` for the natural
(Hessenberg) sum `♯`.
-/
import Mathlib

open Ordinal NaturalOps Order

namespace Frontier

/-- Comparing two ordinals through their quotient and remainder by `P`. -/

theorem div_mod_lt_of_lt {P a b : Ordinal} (hP : P ≠ 0) (h : a < b) :
    a / P < b / P ∨ (a / P = b / P ∧ a % P < b % P) := by
  rcases lt_trichotomy (a / P) (b / P) with h₁ | h₁ | h₁
  · exact Or.inl h₁
  · refine Or.inr ⟨h₁, ?_⟩
    have key : P * (a / P) + a % P < P * (a / P) + b % P := by
      rw [Ordinal.div_add_mod a P, h₁, Ordinal.div_add_mod b P]
      exact h
    exact lt_of_add_lt_add_left key
  · exfalso
    have h2 : b < P * (a / P) := by
      calc b = P * (b / P) + b % P := (Ordinal.div_add_mod b P).symm
        _ < P * (b / P) + P := by
            exact add_lt_add_right (Ordinal.mod_lt b hP) _
        _ = P * (b / P + 1) := by rw [mul_add_one]
        _ ≤ P * (a / P) := by
            exact mul_le_mul_right (Order.add_one_le_iff.2 h₁) P
    have h3 : P * (a / P) ≤ a := Ordinal.mul_div_le a P
    exact absurd (h2.trans_le h3) (not_lt_of_gt h)

/-- If `ω ^ δ` is closed under natural addition, then the natural sum of two ordinals
below `ω ^ δ * ω` is bounded by the expected quotient/remainder expression. -/
