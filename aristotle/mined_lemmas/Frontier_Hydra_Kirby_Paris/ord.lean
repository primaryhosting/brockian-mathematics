/-
Auxiliary ordinal arithmetic: additive principality of `ω ^ γ` for the natural
(Hessenberg) sum `♯`.
-/
import Mathlib

open Ordinal NaturalOps Order

namespace Frontier

/-- Comparing two ordinals through their quotient and remainder by `P`. -/

noncomputable def ord : Hydra → Ordinal.{0}
  | .node l => ordList l

/-- The ordinal measure of a list of hydras: the natural sum of `ω ^ ord tᵢ`. -/
