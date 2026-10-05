/-
Auxiliary ordinal arithmetic: additive principality of `ω ^ γ` for the natural
(Hessenberg) sum `♯`.
-/
import Mathlib

open Ordinal NaturalOps Order

namespace Frontier

/-- Comparing two ordinals through their quotient and remainder by `P`. -/

theorem ordList_append (l₁ l₂ : List Hydra) :
    ordList (l₁ ++ l₂) = ordList l₁ ♯ ordList l₂ := by
  induction l₁ with
  | nil => simp
  | cons t ts ih => simp [ih, nadd_assoc]

/-- If all members of a list have ordinal measure `< γ`, the list's measure is `< ω ^ γ`. -/
