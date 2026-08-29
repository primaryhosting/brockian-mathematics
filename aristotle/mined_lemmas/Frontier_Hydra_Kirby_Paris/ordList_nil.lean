/-
Auxiliary ordinal arithmetic: additive principality of `ω ^ γ` for the natural
(Hessenberg) sum `♯`.
-/
import Mathlib

open Ordinal NaturalOps Order

namespace Frontier

/-- Comparing two ordinals through their quotient and remainder by `P`. -/

@[simp] theorem ordList_nil : ordList [] = 0 := by
  rw [ordList]

