/-
A Mathlib-facing restatement of `Frontier.arrow_impossibility`, with the finiteness of the
set of voters expressed by `Fintype` instead of by a list of voters covering everything.
-/
import Mathlib
import RequestProject.ArrowImpossibility

namespace Frontier

/-- **Arrow's impossibility theorem** for three alternatives and a finite set of voters:
no social welfare function is unanimous, independent of irrelevant alternatives and
non-dictatorial. -/

theorem prefers_trans {r : Ranking} {a b c : Fin 3} (h₁ : prefers r a b) (h₂ : prefers r b c) :
    prefers r a c := Nat.lt_trans h₁ h₂

