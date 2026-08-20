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

def Decisive (F : (V → Ranking) → Ranking) (S : List V) (a b : Fin 3) : Prop :=
  ∀ p : V → Ranking, (∀ v ∈ S, prefers (p v) a b) → prefers (F p) a b

/-- The coalition `S` is *semi-decisive* for `(a, b)`: whenever all of its members prefer `a`
to `b` and everybody else prefers `b` to `a`, society prefers `a` to `b`. -/
