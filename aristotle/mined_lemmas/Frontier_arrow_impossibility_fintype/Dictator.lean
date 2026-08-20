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

def Dictator (F : (V → Ranking) → Ranking) (v : V) : Prop :=
  ∀ (p : V → Ranking) (a b : Fin 3), prefers (p v) a b → prefers (F p) a b

/-! ## Decisive coalitions

Coalitions are represented by lists of voters; only the membership predicate matters. -/

/-- The coalition `S` is *decisive* for the ordered pair `(a, b)`: whenever all of its members
prefer `a` to `b`, so does society. -/
