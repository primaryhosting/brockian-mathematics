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

theorem prefers_asymm {r : Ranking} {a b : Fin 3} (h : prefers r a b) : ¬ prefers r b a :=
  Nat.lt_asymm h

/-- Rankings are total: of two distinct alternatives, one is preferred. -/
