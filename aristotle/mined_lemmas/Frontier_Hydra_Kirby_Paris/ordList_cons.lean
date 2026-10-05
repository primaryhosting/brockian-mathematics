/-
Auxiliary ordinal arithmetic: additive principality of `ω ^ γ` for the natural
(Hessenberg) sum `♯`.
-/
import Mathlib

open Ordinal NaturalOps Order

namespace Frontier

/-- Comparing two ordinals through their quotient and remainder by `P`. -/

@[simp] theorem ordList_cons (t : Hydra) (ts : List Hydra) :
    ordList (t :: ts) = (ω ^ ord t) ♯ ordList ts := by
  rw [ordList]

