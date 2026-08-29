/-
Auxiliary ordinal arithmetic: additive principality of `ω ^ γ` for the natural
(Hessenberg) sum `♯`.
-/
import Mathlib

open Ordinal NaturalOps Order

namespace Frontier

/-- Comparing two ordinals through their quotient and remainder by `P`. -/

noncomputable def ordList : List Hydra → Ordinal.{0}
  | [] => 0
  | t :: ts => (ω ^ ord t) ♯ ordList ts

end

